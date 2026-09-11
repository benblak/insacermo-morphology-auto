#!/usr/bin/env python3
from __future__ import annotations
import io, itertools, json, math, urllib.request, zipfile
from collections import defaultdict
from pathlib import Path
import numpy as np
import pandas as pd

ROOT=Path(__file__).resolve().parent
PRE=ROOT/'INSACERMO_NASA_CMAPSS_FD001_BLIND_PLANNER_PREREG_V1.json'
OUT=ROOT/'nasa_cmapss_fd001_blind_planner_v1_output'; OUT.mkdir(exist_ok=True)
URL='https://data.nasa.gov/docs/legacy/CMAPSSData.zip'

def H(sizes):
    n=sum(sizes)
    return 0.0 if n==0 else -sum((x/n)*math.log2(x/n) for x in sizes if x)

def download_zip():
    with urllib.request.urlopen(URL, timeout=180) as r:
        data=r.read()
    (OUT/'CMAPSSData.zip').write_bytes(data)
    return data

def read_fd001(zbytes):
    z=zipfile.ZipFile(io.BytesIO(zbytes))
    names={n.split('/')[-1]:n for n in z.namelist()}
    need=['test_FD001.txt','RUL_FD001.txt']
    missing=[n for n in need if n not in names]
    if missing: raise RuntimeError(f'missing files in NASA archive: {missing}')
    cols=['unit_id','cycle','setting_1','setting_2','setting_3']+[f'sensor_{i}' for i in range(1,22)]
    test=pd.read_csv(z.open(names['test_FD001.txt']),sep=r'\s+',header=None,names=cols,engine='python')
    rul=pd.read_csv(z.open(names['RUL_FD001.txt']),sep=r'\s+',header=None,names=['RUL'],engine='python')
    return test,rul

def main():
    pre=json.loads(PRE.read_text())
    feats=pre['probe_library']['features']
    zbytes=download_zip(); test,rul=read_fd001(zbytes)
    final=test.sort_values(['unit_id','cycle']).groupby('unit_id',as_index=False).tail(1).sort_values('unit_id').reset_index(drop=True)
    if len(final)!=len(rul): raise RuntimeError(f'unit/RUL mismatch: {len(final)} vs {len(rul)}')
    if len(final)!=100: raise RuntimeError(f'frozen metadata expected 100 test engines, got {len(final)}')
    final['RUL']=rul['RUL'].astype(float).to_numpy()
    if final[feats].isna().any().any(): raise RuntimeError('missing final-cycle frozen probe values')

    Q=pd.DataFrame(index=final.index); binmeta={}
    for f in feats:
        x=final[f].astype(float)
        cuts=np.unique(np.quantile(x.to_numpy(),[.25,.5,.75]))
        edges=np.concatenate(([-np.inf],cuts,[np.inf]))
        Q[f]=pd.cut(x,bins=edges,labels=False,include_lowest=True).astype('Int64').astype(str)
        binmeta[f]={'cuts':[float(v) for v in cuts.tolist()]}

    CONT=1; PLAN=2; IMM=4
    goodmask=[]; zones=[]
    for r in final['RUL'].astype(float):
        if r>=30: goodmask.append(CONT); zones.append('CONTINUE')
        elif r>=10: goodmask.append(PLAN); zones.append('PLAN_SERVICE')
        else: goodmask.append(IMM); zones.append('IMMEDIATE_SERVICE')
    final['zone']=zones
    bmask=CONT|IMM; rmask=CONT|PLAN|IMM

    def ev(sub,cap):
        sub=list(sub); groups=defaultdict(list)
        if not sub: groups[('ALL',)]=list(final.index)
        else:
            for i in final.index: groups[tuple(Q.loc[i,f] for f in sub)].append(i)
        safe=True
        for ids in groups.values():
            common=cap
            for i in ids: common &= goodmask[i]
            if common==0:
                safe=False; break
        sizes=[len(v) for v in groups.values()]
        return {'safe':safe,'cells':len(sizes),'entropy_bits':H(sizes),'max_cell':max(sizes)}

    rows=[]
    for repaired,cap in [(False,bmask),(True,rmask)]:
        for k in range(len(feats)+1):
            for sub in itertools.combinations(feats,k):
                rows.append({'repaired':repaired,'n_probes':k,'probes':list(sub),'total_structural_cost':k+int(repaired),**ev(sub,cap)})
    safe=[r for r in rows if r['safe']]
    def minp(rep):
        ks=[r['n_probes'] for r in safe if r['repaired']==rep]
        return min(ks) if ks else None
    bm,rm=minp(False),minp(True)
    mincost=min((r['total_structural_cost'] for r in safe),default=None)
    opt=[r for r in safe if r['total_structural_cost']==mincost] if mincost is not None else []
    start=ev([],bmask)['safe']; rep0=ev([],rmask)['safe']

    route_types=set()
    for r in opt:
        if not r['repaired'] and r['n_probes']==0: route_types.add('ACT')
        elif not r['repaired'] and r['n_probes']>0: route_types.add('PROBE')
        elif r['repaired'] and r['n_probes']==0: route_types.add('REPAIR')
        else: route_types.add('PROBE+REPAIR')
    if not safe: regime='REFUSE'
    elif len(route_types)==1: regime=next(iter(route_types))
    else: regime='MULTI_ROUTE_FRONTIER:' + '+'.join(sorted(route_types))

    pres=[]
    for r in opt:
        cap=rmask if r['repaired'] else bmask
        for f in r['probes']:
            remain=[x for x in r['probes'] if x!=f]; e=ev(remain,cap)
            pres.append({'repaired':r['repaired'],'terminal_probes':'+'.join(r['probes']),'forgotten_probe':f,'remaining_probes':'+'.join(remain),'safe_after_forgetting':e['safe']})
    rej=sum(not x['safe_after_forgetting'] for x in pres)

    safe_df=pd.DataFrame([{**r,'probes':'+'.join(r['probes'])} for r in safe])
    opt_df=pd.DataFrame([{**r,'probes':'+'.join(r['probes'])} for r in opt])
    safe_df.to_csv(OUT/'safe_states.csv',index=False)
    opt_df.to_csv(OUT/'optimal_frontier.csv',index=False)
    pd.DataFrame(pres).to_csv(OUT/'preserve_forgetting_audit.csv',index=False)
    final[['unit_id','cycle','RUL','zone']+feats].to_csv(OUT/'final_cycle_population.csv',index=False)

    zone_counts=final['zone'].value_counts().to_dict()
    audit={
      'name':'INSACERMO_NASA_CMAPSS_FD001_BLIND_PLANNER_AUDIT_V1',
      'protocol_status':'EXECUTED_AGAINST_FROZEN_PRE_OUTCOME_PREREGISTRATION',
      'regime':regime,
      'source':{'dataset':'NASA C-MAPSS','subset':'FD001','official_download':URL,'test_engines':len(final)},
      'frozen_contract':pre,
      'execution':{
        'population_n':len(final),
        'zone_counts':zone_counts,
        'base_minimum_probes':bm,
        'repaired_minimum_probes':rm,
        'minimum_total_structural_cost':mincost,
        'optimal_terminal_states_n':len(opt),
        'optimal_route_types':sorted(route_types),
        'start_base_safe':start,
        'repair_only_safe':rep0,
        'states_evaluated':len(rows),
        'preserve_tested':len(pres),
        'preserve_rejected':rej
      },
      'feature_binning':binmeta
    }
    (OUT/'AUDIT.json').write_text(json.dumps(audit,indent=2),encoding='utf-8')
    (OUT/'REPORT.md').write_text(f'''# INSACERMO NASA C-MAPSS FD001 blind planner V1\n\n**Protocol:** frozen before `RUL_FD001.txt` outcomes were opened.  \n**Regime:** **{regime}**\n\n- Population: **{len(final)}** engines\n- Action-zone counts: **{zone_counts}**\n- Base minimum probes: **{bm if bm is not None else 'UNREACHABLE'}**\n- Repaired minimum probes: **{rm if rm is not None else 'UNREACHABLE'}**\n- Minimum structural cost: **{mincost if mincost is not None else 'UNREACHABLE'}**\n- Optimal terminal states: **{len(opt)}**\n- Optimal route types: **{', '.join(sorted(route_types)) if route_types else 'NONE'}**\n- Base/no-probe safe: **{start}**\n- REPAIR/no-probe safe: **{rep0}**\n- PRESERVE rejected/tested: **{rej}/{len(pres)}**\n\nThis is a finite structural stress test on simulated aerospace prognostic data, not an aviation maintenance recommendation.\n''',encoding='utf-8')
    print(json.dumps({'regime':regime,'population_n':len(final),'zone_counts':zone_counts,'base_minimum_probes':bm,'repaired_minimum_probes':rm,'minimum_total_structural_cost':mincost,'optimal_terminal_states_n':len(opt),'optimal_route_types':sorted(route_types),'start_base_safe':start,'repair_only_safe':rep0,'preserve_rejected':rej,'preserve_tested':len(pres)},indent=2))

if __name__=='__main__': main()
