#!/usr/bin/env python3
from __future__ import annotations
import csv, hashlib, itertools, json, math, re, urllib.request
from collections import defaultdict
from pathlib import Path
import numpy as np
import pandas as pd

ROOT=Path(__file__).resolve().parent
PRE=ROOT/'INSACERMO_GRAPHS2015_REPAIR_ENVELOPE_PREREG_V1.json'
OUT=ROOT/'graphs2015_repair_envelope_v1_output'; OUT.mkdir(exist_ok=True)
RAW='https://raw.githubusercontent.com/coseal/aslib_data/master/GRAPHS-2015/'

def dl(name):
    p=OUT/name
    with urllib.request.urlopen(RAW+name,timeout=180) as r: p.write_bytes(r.read())
    return p

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def s(v): return v.strip().strip("'").strip('"')
def H(sizes):
    n=sum(sizes); return 0.0 if n==0 else -sum((x/n)*math.log2(x/n) for x in sizes if x)

def parse_arff(path):
    attrs=[]; data=[]; inside=False
    rx=re.compile(r"^@attribute\s+(?:'([^']+)'|\"([^\"]+)\"|(\S+))\s+(.+)$",re.I)
    with path.open('r',encoding='utf-8',errors='replace',newline='') as f:
        for raw in f:
            line=raw.strip()
            if not line or line.startswith('%'): continue
            if not inside:
                if line.lower().startswith('@data'): inside=True; continue
                m=rx.match(line)
                if m: attrs.append((next(x for x in m.groups()[:3] if x is not None),m.group(4).strip()))
            else: data.append(raw)
    rows=[r for r in csv.reader(data) if r]
    if any(len(r)!=len(attrs) for r in rows): raise RuntimeError('ARFF width mismatch')
    return attrs,rows

def main():
    pre=json.loads(PRE.read_text())
    base=pre['actions']['base_capabilities']; adds=pre['actions']['repair_adds_bundle']; allalgs=base+adds
    feats=pre['probe_library']['features']; cutoff=float(pre['dataset']['cutoff_seconds'])
    ap,fp,dp=dl('algorithm_runs.arff'),dl('feature_values.arff'),dl('description.txt')
    aa,ar=parse_arff(ap); cols=[x[0] for x in aa]; ci={c:i for i,c in enumerate(cols)}
    tcol='runtime' if 'runtime' in ci else ('time' if 'time' in ci else ('PAR10' if 'PAR10' in ci else None))
    req=['instance_id','repetition','algorithm','runstatus']
    if tcol is None or any(c not in ci for c in req): raise RuntimeError(f'unexpected algorithm schema {cols}')
    wanted=set(allalgs); rec=[]
    for r in ar:
        inst=s(r[ci['instance_id']]); rep=int(float(s(r[ci['repetition']]))); alg=s(r[ci['algorithm']]); st=s(r[ci['runstatus']])
        rawrt=s(r[ci[tcol]])
        try: rt=float(rawrt)
        except: rt=float('inf')
        if alg in wanted: rec.append((inst,rep,alg,rt,st))
    counts=defaultdict(int)
    for inst,rep,alg,rt,st in rec: counts[(inst,alg)]+=1
    bad=[k for k,v in counts.items() if v!=1]
    if bad: raise RuntimeError(f'duplicate/missing deterministic records: {bad[:10]}')
    good=defaultdict(dict)
    for inst,rep,alg,rt,st in rec: good[inst][alg]=(st=='ok' and rt<cutoff)
    insts=sorted({x[0] for x in rec}); complete=[i for i in insts if all(a in good[i] for a in allalgs)]
    cohort=[i for i in complete if any(good[i][a] for a in base)]
    if not cohort: raise RuntimeError('empty frozen cohort')

    fa,fr=parse_arff(fp); fcols=[x[0] for x in fa]; fi={c:j for j,c in enumerate(fcols)}
    miss=[f for f in feats if f not in fi]
    if miss: raise RuntimeError(f'frozen features missing: {miss}')
    by={}
    for r in fr:
        inst=s(r[fi['instance_id']]); by[inst]={f:s(r[fi[f]]) for f in feats}
    raw=pd.DataFrame(index=cohort,columns=feats,dtype=object)
    for i in cohort:
        vals=by.get(i,{})
        for f in feats: raw.loc[i,f]=vals.get(f,'?')
    Q=pd.DataFrame(index=cohort); binmeta={}
    for f in feats:
        ss=raw[f].astype(str); non=ss!='?'; num=pd.to_numeric(ss.where(non),errors='coerce')
        if non.sum()>0 and int(num.notna().sum())==int(non.sum()):
            cuts=np.unique(np.quantile(num.dropna().to_numpy(float),[.25,.5,.75])); edges=np.concatenate(([-np.inf],cuts,[np.inf]))
            b=pd.cut(num,bins=edges,labels=False,include_lowest=True); Q[f]=b.astype('Int64').astype(str); Q.loc[~non,f]='MISSING'
            binmeta[f]={'kind':'numeric_quartile','cuts':[float(x) for x in cuts]}
        else:
            Q[f]=ss.where(non,'MISSING'); binmeta[f]={'kind':'categorical','levels':sorted(Q[f].unique().tolist())}

    bits={a:(1<<j) for j,a in enumerate(allalgs)}
    gm={}
    for i in cohort:
        m=0
        for a,b in bits.items():
            if good[i][a]: m|=b
        gm[i]=m
    bmask=sum(bits[a] for a in base); rmask=sum(bits[a] for a in allalgs)
    def ev(sub,cap):
        groups=defaultdict(list); sub=list(sub)
        if not sub: groups[('ALL',)]=cohort
        else:
            for i in cohort: groups[tuple(Q.loc[i,f] for f in sub)].append(i)
        common_by_cell=[]
        safe=True
        for key,ids in groups.items():
            common=cap
            for i in ids: common &= gm[i]
            common_by_cell.append((key,common))
            if common==0: safe=False
        sizes=[len(v) for v in groups.values()]
        return {'safe':safe,'cells':len(sizes),'entropy_bits':H(sizes),'max_cell':max(sizes)}

    rows=[]
    for repaired,cap in [(False,bmask),(True,rmask)]:
        for k in range(len(feats)+1):
            for sub in itertools.combinations(feats,k):
                rows.append({'repaired':repaired,'n_probes':k,'probes':list(sub),'total_structural_cost':k+int(repaired),**ev(sub,cap)})
    def minp(rep):
        ks=[r['n_probes'] for r in rows if r['repaired']==rep and r['safe']]
        return min(ks) if ks else None
    bm,rm=minp(False),minp(True); safe=[r for r in rows if r['safe']]
    mincost=min((r['total_structural_cost'] for r in safe),default=None)
    opt=[r for r in safe if r['total_structural_cost']==mincost] if mincost is not None else []
    start=ev([],bmask)['safe']; repair0=ev([],rmask)['safe']
    anybp=any(r['safe'] and not r['repaired'] and r['n_probes']>0 for r in rows)
    anyrp=any(r['safe'] and r['repaired'] and r['n_probes']>0 for r in rows)
    act_immediate=start
    repair_only=(not start) and repair0 and mincost==1
    if act_immediate: regime='ACT_IMMEDIATE'
    elif repair_only: regime='REPAIR_ONLY'
    elif not safe: regime='REFUSE_NO_REACHABLE_SAFE_STATE'
    else:
        kinds=set()
        for r in opt:
            if r['repaired'] and r['n_probes']>0: kinds.add('PROBE_REPAIR')
            elif r['repaired']: kinds.add('REPAIR_ONLY')
            elif r['n_probes']>0: kinds.add('PROBE_ONLY')
            else: kinds.add('ACT_IMMEDIATE')
        regime=next(iter(kinds)) if len(kinds)==1 else 'MULTI_ROUTE_FRONTIER:' + '+'.join(sorted(kinds))

    universal_base=[a for a in base if all(good[i][a] for i in cohort)]
    universal_added=[a for a in adds if all(good[i][a] for i in cohort)]
    pres=[]
    for r in opt:
        cap=rmask if r['repaired'] else bmask
        for f in r['probes']:
            remain=[x for x in r['probes'] if x!=f]; e=ev(remain,cap)
            pres.append({'repaired':r['repaired'],'terminal_probes':'+'.join(r['probes']),'forgotten_probe':f,'remaining_probes':'+'.join(remain),'safe_after_forgetting':e['safe']})
    rej=sum(not x['safe_after_forgetting'] for x in pres)
    pd.DataFrame([{**r,'probes':'+'.join(r['probes'])} for r in safe]).to_csv(OUT/'safe_states.csv',index=False)
    pd.DataFrame([{**r,'probes':'+'.join(r['probes'])} for r in opt]).to_csv(OUT/'optimal_frontier.csv',index=False)
    pd.DataFrame(pres).to_csv(OUT/'preserve_forgetting_audit.csv',index=False)
    audit={'name':'INSACERMO_GRAPHS2015_REPAIR_ENVELOPE_AUDIT_V1','protocol_status':'EXECUTED_AGAINST_FROZEN_PRE_OUTCOME_PREREGISTRATION','regime':regime,'source':{'scenario':'GRAPHS-2015','runtime_measure_column_used':tcol,'algorithm_runs_sha256':sha(ap),'feature_values_sha256':sha(fp),'description_sha256':sha(dp),'algorithm_rows_total':len(ar),'feature_rows_total':len(fr)},'frozen_contract':pre,'execution':{'instances_complete_for_frozen_algorithms':len(complete),'fixed_base_actionable_cohort_n':len(cohort),'base_good_counts':{a:sum(good[i][a] for i in cohort) for a in base},'added_good_counts':{a:sum(good[i][a] for i in cohort) for a in adds},'states_evaluated':len(rows),'base_minimum_probes':bm,'repaired_minimum_probes':rm,'minimum_total_structural_cost':mincost,'optimal_terminal_states_n':len(opt),'start_base_safe':start,'repair_bundle_only_safe':repair0,'act_immediate':act_immediate,'repair_only':repair_only,'any_probe_only_safe':anybp,'any_repair_plus_probe_safe':anyrp,'universal_base_actions':universal_base,'universal_added_actions':universal_added,'preserve_tested':len(pres),'preserve_rejected':rej},'feature_binning':binmeta}
    (OUT/'AUDIT.json').write_text(json.dumps(audit,indent=2),encoding='utf-8')
    (OUT/'REPORT.md').write_text(f'''# INSACERMO GRAPHS-2015 repair-envelope blind test V1\n\n**Protocol:** frozen before `algorithm_runs.arff` was opened.  \n**Regime:** **{regime}**\n\n- Cohort: **{len(cohort)}**\n- Base minimum probes: **{bm if bm is not None else 'UNREACHABLE'}**\n- Repaired minimum probes: **{rm if rm is not None else 'UNREACHABLE'}**\n- Minimum structural cost: **{mincost if mincost is not None else 'UNREACHABLE'}**\n- Base/no-probe safe: **{start}**\n- Portfolio-REPAIR/no-probe safe: **{repair0}**\n- ACT immediate: **{act_immediate}**\n- REPAIR only: **{repair_only}**\n- Universal base actions: **{', '.join(universal_base) if universal_base else 'NONE'}**\n- Universal newly added actions: **{', '.join(universal_added) if universal_added else 'NONE'}**\n- Optimal terminal states: **{len(opt)}**\n- PRESERVE rejected/tested: **{rej}/{len(pres)}**\n''',encoding='utf-8')
    print(json.dumps({'regime':regime,'cohort_n':len(cohort),'base_minimum_probes':bm,'repaired_minimum_probes':rm,'minimum_total_structural_cost':mincost,'start_base_safe':start,'repair_bundle_only_safe':repair0,'act_immediate':act_immediate,'repair_only':repair_only,'universal_base_actions':universal_base,'universal_added_actions':universal_added,'optimal_terminal_states_n':len(opt),'preserve_rejected':rej,'preserve_tested':len(pres)},indent=2))
if __name__=='__main__': main()
