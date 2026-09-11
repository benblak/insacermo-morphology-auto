#!/usr/bin/env python3
from __future__ import annotations
import csv, hashlib, itertools, json, math, re, urllib.request
from collections import defaultdict
from pathlib import Path
import numpy as np
import pandas as pd

ROOT=Path(__file__).resolve().parent
PREREG=ROOT/'INSACERMO_CSPMZN2013_BLIND_PLANNER_PREREG_V1.json'
OUT=ROOT/'cspmzn2013_blind_planner_v1_output'; OUT.mkdir(exist_ok=True)
RAW='https://raw.githubusercontent.com/coseal/aslib_data/master/CSP-MZN-2013/'

def dl(name):
    p=OUT/name
    with urllib.request.urlopen(RAW+name,timeout=180) as r: p.write_bytes(r.read())
    return p

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def parse_arff(path):
    attrs=[]; data=[]; in_data=False
    rx=re.compile(r"^@attribute\s+(?:'([^']+)'|\"([^\"]+)\"|(\S+))\s+(.+)$",re.I)
    with path.open('r',encoding='utf-8',errors='replace',newline='') as f:
        for raw in f:
            line=raw.strip()
            if not line or line.startswith('%'): continue
            if not in_data:
                if line.lower().startswith('@data'): in_data=True; continue
                m=rx.match(line)
                if m:
                    name=next(x for x in m.groups()[:3] if x is not None)
                    attrs.append((name,m.group(4).strip()))
            else: data.append(raw)
    rows=[r for r in csv.reader(data) if r]
    if not attrs: raise RuntimeError(f'No attributes in {path}')
    bad=[(i,len(r)) for i,r in enumerate(rows) if len(r)!=len(attrs)]
    if bad: raise RuntimeError(f'ARFF width mismatch: {bad[:5]} vs {len(attrs)} attrs')
    return attrs,rows

def s(v): return v.strip().strip("'").strip('"')
def H(sizes):
    n=sum(sizes)
    return 0.0 if n==0 else -sum((x/n)*math.log2(x/n) for x in sizes if x)

def main():
    pre=json.loads(PREREG.read_text(encoding='utf-8'))
    base=pre['actions']['base_capabilities']; repair=pre['actions']['repair_adds']; feats=pre['probe_library']['features']; cutoff=float(pre['dataset']['cutoff_seconds'])
    ap,fp,dp=dl('algorithm_runs.arff'),dl('feature_values.arff'),dl('description.txt')
    aa,ar=parse_arff(ap); ac=[x[0] for x in aa]; ai={c:j for j,c in enumerate(ac)}
    required=['instance_id','repetition','algorithm','runtime','runstatus']
    missing=[c for c in required if c not in ai]
    if missing: raise RuntimeError(f'Unexpected algorithm schema, missing {missing}; got {ac}')
    wanted=set(base+[repair]); rec=[]
    for r in ar:
        inst=s(r[ai['instance_id']]); rep=s(r[ai['repetition']]); alg=s(r[ai['algorithm']]); rt=s(r[ai['runtime']]); st=s(r[ai['runstatus']])
        if alg in wanted:
            rec.append((inst,int(float(rep)),alg,float(rt),st))
    counts=defaultdict(int)
    for inst,rep,alg,rt,st in rec: counts[(inst,alg)]+=1
    dup=[k for k,v in counts.items() if v!=1]
    if dup: raise RuntimeError(f'duplicate/missing deterministic records: {dup[:10]}')
    good=defaultdict(dict)
    for inst,rep,alg,rt,st in rec: good[inst][alg]=(st=='ok' and rt<cutoff)
    insts=sorted({x[0] for x in rec}); complete=[i for i in insts if all(a in good[i] for a in wanted)]
    cohort=[i for i in complete if any(good[i][a] for a in base)]
    if not cohort: raise RuntimeError('empty frozen cohort')

    fa,fr=parse_arff(fp); fc=[x[0] for x in fa]; idx={c:j for j,c in enumerate(fc)}
    miss=[f for f in feats if f not in idx]
    if 'instance_id' not in idx or miss: raise RuntimeError(f'frozen features missing: {miss}; instance_id present={"instance_id" in idx}')
    by={}
    for r in fr:
        inst=s(r[idx['instance_id']]); by[inst]={f:s(r[idx[f]]) for f in feats}
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

    bits={base[0]:1,base[1]:2,repair:4}; gm={}
    for i in cohort:
        m=0
        for a,b in bits.items():
            if good[i][a]: m|=b
        gm[i]=m
    bmask=bits[base[0]]|bits[base[1]]; rmask=bmask|bits[repair]
    def ev(sub,cap):
        sub=list(sub); groups=defaultdict(list)
        if not sub: groups[('ALL',)]=cohort
        else:
            for i in cohort: groups[tuple(Q.loc[i,f] for f in sub)].append(i)
        safe=True; bad=[]
        for key,ids in groups.items():
            common=cap
            for i in ids: common &= gm[i]
            if common==0:
                safe=False
                if len(bad)<20: bad.append({'cell':list(key),'n':len(ids),'examples':ids[:10]})
        sizes=[len(v) for v in groups.values()]
        return {'safe':safe,'cells':len(sizes),'entropy_bits':H(sizes),'max_cell':max(sizes),'bad_cells_sample':bad}

    rows=[]
    for repaired,cap in [(False,bmask),(True,rmask)]:
        for k in range(len(feats)+1):
            for sub in itertools.combinations(feats,k):
                rows.append({'repaired':repaired,'n_probes':k,'probes':list(sub),'total_structural_cost':k+int(repaired),**ev(sub,cap)})
    def minp(rep):
        ks=[r['n_probes'] for r in rows if r['repaired']==rep and r['safe']]
        return min(ks) if ks else None
    bm,rm=minp(False),minp(True); safe=[r for r in rows if r['safe']]
    mincost=min((r['total_structural_cost'] for r in safe),default=None); opt=[r for r in safe if r['total_structural_cost']==mincost] if mincost is not None else []
    start=ev([],bmask)['safe']; ro=ev([],rmask)['safe']; anybp=any(r['safe'] and not r['repaired'] and r['n_probes']>0 for r in rows); anyrp=any(r['safe'] and r['repaired'] and r['n_probes']>0 for r in rows)
    strong=(not start) and (not anybp) and (not ro) and anyrp
    if rm is not None and (bm is None or rm<bm): verdict='STRONG_POSITIVE_STRUCTURAL_REPLICATION' if bm is None else 'POSITIVE_CAPABILITY_INFORMATION_REPLICATION'
    elif bm is not None and rm==bm: verdict='NULL_NO_INFORMATION_REDUCTION'
    elif rm is not None and bm is not None and rm>bm: verdict='NEGATIVE_REPAIR_INCREASES_INFORMATION_REQUIREMENT'
    else: verdict='NO_SAFE_REPRESENTATION_IN_FROZEN_SEARCH_SPACE'
    route=set()
    for r in opt:
        if r['repaired'] and r['n_probes']>0: route.update(['PROBE','REPAIR'])
        elif r['repaired']: route.add('REPAIR')
        elif r['n_probes']>0: route.add('PROBE')
        else: route.add('ACT')
    pres=[]
    for r in opt:
        cap=rmask if r['repaired'] else bmask
        for f in r['probes']:
            remain=[x for x in r['probes'] if x!=f]; e=ev(remain,cap)
            pres.append({'repaired':r['repaired'],'terminal_probes':'+'.join(r['probes']),'forgotten_probe':f,'remaining_probes':'+'.join(remain),'safe_after_forgetting':e['safe']})
    rej=sum(not x['safe_after_forgetting'] for x in pres)

    pd.DataFrame([{**{k:v for k,v in r.items() if k!='bad_cells_sample'},'probes':'+'.join(r['probes'])} for r in safe]).to_csv(OUT/'safe_states.csv',index=False)
    pd.DataFrame([{**{k:v for k,v in r.items() if k!='bad_cells_sample'},'probes':'+'.join(r['probes'])} for r in opt]).to_csv(OUT/'optimal_frontier.csv',index=False)
    pd.DataFrame(pres).to_csv(OUT/'preserve_forgetting_audit.csv',index=False)
    ep=[]
    for rep in [False,True]:
        rr=[r for r in rows if r['repaired']==rep]; mk=min((r['n_probes'] for r in rr if r['safe']),default=None); mins=[r for r in rr if r['safe'] and r['n_probes']==mk] if mk is not None else []
        ep.append({'regime':'base' if not rep else 'base_plus_repair','minimum_probes':mk,'n_min_probe_safe_states':len(mins),'best_entropy_at_min_probes':min((r['entropy_bits'] for r in mins),default=None),'fewest_cells_at_min_probes':min((r['cells'] for r in mins),default=None)})
    pd.DataFrame(ep).to_csv(OUT/'primary_endpoints.csv',index=False)

    audit={'name':'INSACERMO_CSPMZN2013_BLIND_PLANNER_AUDIT_V1','protocol_status':'EXECUTED_AGAINST_FROZEN_PRE_OUTCOME_PREREGISTRATION','verdict':verdict,'source':{'scenario':'CSP-MZN-2013','algorithm_runs_sha256':sha(ap),'feature_values_sha256':sha(fp),'description_sha256':sha(dp),'algorithm_rows_total':len(ar),'feature_rows_total':len(fr),'algorithm_schema':ac},'frozen_contract':pre,'execution':{'instances_complete_for_frozen_algorithms':len(complete),'fixed_base_actionable_cohort_n':len(cohort),'base_good_counts':{a:sum(good[i][a] for i in cohort) for a in base},'repair_good_count':sum(good[i][repair] for i in cohort),'states_evaluated':len(rows),'base_minimum_probes':bm,'repaired_minimum_probes':rm,'minimum_total_structural_cost':mincost,'optimal_terminal_states_n':len(opt),'optimal_first_move_route_kinds':sorted(route),'start_base_safe':start,'repair_only_safe':ro,'any_probe_only_safe':anybp,'any_repair_plus_probe_safe':anyrp,'strong_mixed_route':strong,'preserve_tested':len(pres),'preserve_rejected':rej},'feature_binning':binmeta}
    (OUT/'AUDIT.json').write_text(json.dumps(audit,indent=2),encoding='utf-8')
    report=f'''# INSACERMO CSP-MZN-2013 blind planner replication V1\n\n**Protocol:** frozen before `algorithm_runs.arff` was opened.  \n**Verdict under frozen rules:** **{verdict}**\n\n## Primary endpoints\n\n- Fixed base-actionable cohort: **{len(cohort)}** instances\n- Frozen base algorithms: `{base[0]}`, `{base[1]}`\n- Frozen REPAIR: add `{repair}`\n- Minimum frozen coarse probes under base: **{bm if bm is not None else 'UNREACHABLE'}**\n- Minimum frozen coarse probes after REPAIR: **{rm if rm is not None else 'UNREACHABLE'}**\n- Minimum total structural cost: **{mincost if mincost is not None else 'UNREACHABLE'}**\n- Optimal terminal states: **{len(opt)}**\n- Optimal first-move route kinds: **{', '.join(sorted(route)) if route else 'NONE'}**\n\nStart/base/no-probe safe: **{start}**  \nAny probe-only safe representation: **{anybp}**  \nREPAIR-only/no-probe safe: **{ro}**  \nAny REPAIR+PROBE safe representation: **{anyrp}**  \nStrong mixed-route predicate: **{strong}**\n\n## PRESERVE\n\nSingle-probe forgetting edges tested from optimal terminals: **{len(pres)}**  \nRejected because safety is lost: **{rej}**\n\n## Scope\n\nPre-specified fourth-domain deterministic structural test. Results were not used to revise the frozen protocol.\n'''
    (OUT/'REPORT.md').write_text(report,encoding='utf-8')
    print(json.dumps({'verdict':verdict,'cohort_n':len(cohort),'base_minimum_probes':bm,'repaired_minimum_probes':rm,'minimum_total_structural_cost':mincost,'optimal_terminal_states_n':len(opt),'optimal_first_move_route_kinds':sorted(route),'strong_mixed_route':strong,'preserve_rejected':rej,'preserve_tested':len(pres)},indent=2))
if __name__=='__main__': main()
