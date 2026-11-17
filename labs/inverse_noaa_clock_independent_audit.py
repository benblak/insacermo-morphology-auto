#!/usr/bin/env python3
"""Independent raw-byte NOAA phase audit; no import from discovery learner."""
import gzip,hashlib,json,sys
from datetime import datetime,timezone
from pathlib import Path
BASE=datetime(2000,1,1,tzinfo=timezone.utc)
SOURCES=[('41002',2023),('42002',2023),('46002',2023),('41002',2024),('42002',2024)]
CHANNELS={'WVHT':(0,40),'APD':(1,25),'WSPD':(0,75)}
def extract(raw):
    fields=None;rows=[]
    for line in raw.decode('utf8').splitlines():
        if line.startswith('#'):
            h=line.lstrip('#').split()
            if 'WVHT' in h and 'WSPD' in h:fields={k:i for i,k in enumerate(h)}
            continue
        if not fields or not line.strip():continue
        vals=line.split()
        if len(vals)<len(fields):continue
        try:
            y=int(vals[fields.get('YY',fields.get('YYYY'))])
            if y<100:y=y+(2000 if y<70 else 1900)
            dt=datetime(y,int(vals[fields['MM']]),int(vals[fields['DD']]),
                int(vals[fields['hh']]),int(vals[fields['mm']]),tzinfo=timezone.utc)
            slot=int((dt-BASE).total_seconds()//600)
            b={name:int(lo<=float(vals[fields[name]])<=hi) for name,(lo,hi) in CHANNELS.items()}
            rows.append((slot,b))
        except (ValueError,IndexError,OverflowError):continue
    return rows
def check(rows,seal,name):
    model=seal['models'][name]['model'];p=model['period_slots'];pr=model['phase_probability']
    phase=[[0,0] for _ in range(p)]
    tp=fp=fn=tn=0;brier=0
    for slot,bits in rows:
        y=bits[name];phase[slot%p][y]+=1
        prob=pr[slot%p];pred=int(prob>=.5)
        brier+=(prob-y)**2
        if pred and y:tp+=1
        elif pred:fp+=1
        elif y:fn+=1
        else:tn+=1
    return dict(rows=len(rows),phase_counts=phase,confusion=dict(tp=tp,fp=fp,fn=fn,tn=tn),
        f1=2*tp/(2*tp+fp+fn) if 2*tp+fp+fn else 0,brier=brier/len(rows))
def main(folder):
    root=Path(folder);seal_file=root/'sealed_before_validation.json'
    seal=json.loads(seal_file.read_text());audit=json.loads((root/'audit.json').read_text())
    assert hashlib.sha256(seal_file.read_bytes()).hexdigest()==audit['seal_sha256']
    assert [seal['models'][k]['model']['period_slots'] for k in ('WVHT','APD','WSPD')]==[3,3,1]
    checks=[]
    for ix,(st,yr) in enumerate(SOURCES):
        payload=(root/'raw_noaa'/f'{st}h{yr}.txt.gz').read_bytes()
        origin=audit['all_sources'][ix]
        assert hashlib.sha256(payload).hexdigest()==origin['gzip_sha256']
        plain=gzip.decompress(payload)
        assert hashlib.sha256(plain).hexdigest()==origin['decompressed_sha256']
        rows=extract(plain)
        for channel in CHANNELS:
            got=check(rows,seal,channel)
            expected=seal['train_checks'][channel] if ix==0 else audit['validation'][ix-1]['channels'][channel]
            for key in ('rows','phase_counts','confusion'):
                assert got[key]==expected[key],(st,yr,channel,key)
            for key in ('f1','brier'):
                assert abs(got[key]-expected[key])<1e-13,(st,yr,channel,key)
        w=check(rows,seal,'WVHT')
        checks.append(dict(station=st,year=yr,rows=len(rows),wave_phase_counts=w['phase_counts'],f1=w['f1']))
    assert audit['verdict']=='INVERSE_OBSERVATION_CLOCK_PASS'
    receipt=dict(verdict='INDEPENDENT_NOAA_CLOCK_PASS',raw_archives=5,channel_checks=15,
       seal_sha256=audit['seal_sha256'],cases=checks)
    (root/'independent_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('INDEPENDENT_NOAA_CLOCK_PASS: 5 raw archives, 15 independently recomputed channel scores')
if __name__=='__main__':main(sys.argv[1] if len(sys.argv)>1 else '/tmp/insacermo_inverse_clock')
