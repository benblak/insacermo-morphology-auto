#!/usr/bin/env python3
from __future__ import annotations
import hashlib, io, itertools, json, math, urllib.request
from collections import defaultdict
from pathlib import Path
import numpy as np
import pandas as pd

ROOT = Path(__file__).resolve().parent
PRE = ROOT / 'INSACERMO_NASA_CMAPSS_FD001_BLIND_PLANNER_PREREG_V1.json'
NOTE = ROOT / 'INSACERMO_NASA_CMAPSS_FD001_RETRIEVAL_COMPATIBILITY_NOTE_V1.json'
OUT = ROOT / 'nasa_cmapss_fd001_blind_planner_v1b_output'
OUT.mkdir(exist_ok=True)
MIRROR_COMMIT = 'ffca02f70f3ce41042f1a8ec1d82ea7ad13cf2a1'
BASE = f'https://raw.githubusercontent.com/ericlrf/rul/{MIRROR_COMMIT}/CMAPSSData/'
FILES = {'test':'test_FD001.txt','rul':'RUL_FD001.txt'}


def get_bytes(name: str) -> bytes:
    req = urllib.request.Request(BASE + name, headers={'User-Agent':'INSACERMO-retrieval-fix/1.0'})
    with urllib.request.urlopen(req, timeout=120) as r:
        data = r.read()
    if not data:
        raise RuntimeError(f'empty download: {name}')
    return data


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def entropy(sizes):
    n = sum(sizes)
    return 0.0 if n == 0 else -sum((x/n)*math.log2(x/n) for x in sizes if x)


def main():
    pre = json.loads(PRE.read_text())
    note = json.loads(NOTE.read_text())
    assert pre['status'] == 'FROZEN_BEFORE_FD001_TEST_RUL_OPENED'
    assert note['methodological_status'] == 'PRESERVES_ORIGINAL_FROZEN_PROTOCOL'

    test_b = get_bytes(FILES['test'])
    rul_b = get_bytes(FILES['rul'])
    (OUT / FILES['test']).write_bytes(test_b)
    (OUT / FILES['rul']).write_bytes(rul_b)

    cols = ['unit_id','cycle','setting_1','setting_2','setting_3'] + [f'sensor_{i}' for i in range(1,22)]
    test = pd.read_csv(io.BytesIO(test_b), sep=r'\s+', header=None, names=cols, engine='python')
    rul = pd.read_csv(io.BytesIO(rul_b), sep=r'\s+', header=None, names=['RUL'], engine='python')
    final = test.sort_values(['unit_id','cycle']).groupby('unit_id', as_index=False).tail(1).sort_values('unit_id').reset_index(drop=True)

    if len(final) != 100 or len(rul) != 100:
        raise RuntimeError(f'frozen metadata expected 100 engines/RULs, got {len(final)}/{len(rul)}')
    if final['unit_id'].nunique() != 100:
        raise RuntimeError('expected 100 unique engine ids')

    feats = pre['probe_library']['features']
    final['RUL'] = rul['RUL'].astype(float).to_numpy()
    if final[feats].isna().any().any():
        raise RuntimeError('missing final-cycle frozen probe values')

    Q = pd.DataFrame(index=final.index)
    binmeta = {}
    for f in feats:
        x = final[f].astype(float)
        cuts = np.unique(np.quantile(x.to_numpy(), [.25,.5,.75]))
        edges = np.concatenate(([-np.inf], cuts, [np.inf]))
        Q[f] = pd.cut(x, bins=edges, labels=False, include_lowest=True).astype('Int64').astype(str)
        binmeta[f] = {'cuts':[float(v) for v in cuts]}

    CONT, PLAN, IMM = 1, 2, 4
    goodmask, zones = [], []
    for r in final['RUL'].astype(float):
        if r >= 30:
            goodmask.append(CONT); zones.append('CONTINUE')
        elif r >= 10:
            goodmask.append(PLAN); zones.append('PLAN_SERVICE')
        else:
            goodmask.append(IMM); zones.append('IMMEDIATE_SERVICE')
    final['zone'] = zones
    bmask, rmask = CONT | IMM, CONT | PLAN | IMM

    def evaluate(subset, capmask):
        subset = list(subset)
        groups = defaultdict(list)
        if not subset:
            groups[('ALL',)] = list(final.index)
        else:
            for i in final.index:
                groups[tuple(Q.loc[i, f] for f in subset)].append(i)
        safe = True
        for ids in groups.values():
            common = capmask
            for i in ids:
                common &= goodmask[i]
            if common == 0:
                safe = False
                break
        sizes = [len(v) for v in groups.values()]
        return {'safe':safe,'cells':len(sizes),'entropy_bits':entropy(sizes),'max_cell':max(sizes)}

    rows = []
    for repaired, cap in [(False,bmask),(True,rmask)]:
        for k in range(len(feats)+1):
            for sub in itertools.combinations(feats, k):
                rows.append({'repaired':repaired,'n_probes':k,'probes':list(sub),
                             'total_structural_cost':k+int(repaired), **evaluate(sub, cap)})

    safe = [r for r in rows if r['safe']]
    def minp(repaired):
        ks = [r['n_probes'] for r in safe if r['repaired'] == repaired]
        return min(ks) if ks else None
    bm, rm = minp(False), minp(True)
    mincost = min((r['total_structural_cost'] for r in safe), default=None)
    opt = [r for r in safe if r['total_structural_cost'] == mincost] if mincost is not None else []
    start = evaluate([], bmask)['safe']
    rep0 = evaluate([], rmask)['safe']

    route_types = set()
    for r in opt:
        if not r['repaired'] and r['n_probes'] == 0: route_types.add('ACT')
        elif not r['repaired']: route_types.add('PROBE')
        elif r['n_probes'] == 0: route_types.add('REPAIR')
        else: route_types.add('PROBE+REPAIR')
    if not safe:
        regime = 'REFUSE'
    elif len(route_types) == 1:
        regime = next(iter(route_types))
    else:
        regime = 'MULTI_ROUTE_FRONTIER:' + '+'.join(sorted(route_types))

    pres = []
    for r in opt:
        cap = rmask if r['repaired'] else bmask
        for f in r['probes']:
            remain = [x for x in r['probes'] if x != f]
            e = evaluate(remain, cap)
            pres.append({'repaired':r['repaired'],'terminal_probes':'+'.join(r['probes']),
                         'forgotten_probe':f,'remaining_probes':'+'.join(remain),
                         'safe_after_forgetting':e['safe']})
    rej = sum(not x['safe_after_forgetting'] for x in pres)

    pd.DataFrame([{**r,'probes':'+'.join(r['probes'])} for r in safe]).to_csv(OUT/'safe_states.csv', index=False)
    pd.DataFrame([{**r,'probes':'+'.join(r['probes'])} for r in opt]).to_csv(OUT/'optimal_frontier.csv', index=False)
    pd.DataFrame(pres).to_csv(OUT/'preserve_forgetting_audit.csv', index=False)
    final[['unit_id','cycle','RUL','zone'] + feats].to_csv(OUT/'final_cycle_population.csv', index=False)

    zone_counts = final['zone'].value_counts().to_dict()
    source = {
        'dataset':'NASA C-MAPSS', 'subset':'FD001',
        'official_download':pre['source_metadata']['official_download'],
        'retrieval_mode':'PINNED_PUBLIC_GITHUB_MIRROR_AFTER_OFFICIAL_TIMEOUT',
        'mirror_repository':'ericlrf/rul', 'mirror_commit':MIRROR_COMMIT,
        'test_file_sha256':sha256(test_b), 'rul_file_sha256':sha256(rul_b)
    }
    audit = {
        'name':'INSACERMO_NASA_CMAPSS_FD001_BLIND_PLANNER_AUDIT_V1B',
        'protocol_status':'EXECUTED_AGAINST_ORIGINAL_FROZEN_PRE_OUTCOME_PREREGISTRATION_WITH_RETRIEVAL_ONLY_FIX',
        'regime':regime, 'source':source, 'frozen_contract':pre, 'retrieval_compatibility_note':note,
        'execution':{
            'population_n':len(final), 'zone_counts':zone_counts,
            'base_minimum_probes':bm, 'repaired_minimum_probes':rm,
            'minimum_total_structural_cost':mincost,
            'optimal_terminal_states_n':len(opt), 'optimal_route_types':sorted(route_types),
            'start_base_safe':start, 'repair_only_safe':rep0,
            'states_evaluated':len(rows), 'preserve_tested':len(pres), 'preserve_rejected':rej
        },
        'feature_binning':binmeta
    }
    (OUT/'AUDIT.json').write_text(json.dumps(audit, indent=2), encoding='utf-8')
    (OUT/'REPORT.md').write_text(f'''# INSACERMO NASA C-MAPSS FD001 blind planner V1B\n\n**Original preregistration:** frozen before `RUL_FD001.txt` outcomes were opened.  \n**Mechanical compatibility fix only:** pinned mirror retrieval after NASA endpoint timeout.  \n**Regime:** **{regime}**\n\n- Population: **{len(final)}** engines\n- Action-zone counts: **{zone_counts}**\n- Base minimum probes: **{bm if bm is not None else 'UNREACHABLE'}**\n- Repaired minimum probes: **{rm if rm is not None else 'UNREACHABLE'}**\n- Minimum structural cost: **{mincost if mincost is not None else 'UNREACHABLE'}**\n- Optimal terminal states: **{len(opt)}**\n- Optimal route types: **{', '.join(sorted(route_types)) if route_types else 'NONE'}**\n- Base/no-probe safe: **{start}**\n- REPAIR/no-probe safe: **{rep0}**\n- PRESERVE rejected/tested: **{rej}/{len(pres)}**\n\nThis is a finite structural stress test on simulated aerospace prognostic data, not an aviation maintenance recommendation.\n''', encoding='utf-8')

    print(json.dumps({'regime':regime,'population_n':len(final),'zone_counts':zone_counts,
                      'base_minimum_probes':bm,'repaired_minimum_probes':rm,
                      'minimum_total_structural_cost':mincost,'optimal_terminal_states_n':len(opt),
                      'optimal_route_types':sorted(route_types),'start_base_safe':start,
                      'repair_only_safe':rep0,'preserve_rejected':rej,'preserve_tested':len(pres),
                      'test_file_sha256':sha256(test_b),'rul_file_sha256':sha256(rul_b)}, indent=2))

if __name__ == '__main__':
    main()
