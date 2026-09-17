import itertools, os, hashlib
from collections import Counter, deque
import numpy as np
from scipy.io import loadmat

CONN=os.environ.get('INSACERMO_CELEGANS_CONN','/tmp/ConnOrdered_040903.mat')
TYPES=os.environ.get('INSACERMO_CELEGANS_TYPES','/tmp/NeuronTypeOrdered_040903.mat')
H=4
MAX_BUNDLE=3
DELETE_LEVELS=(4,8,12)
HASH_CONTROL=8
PERMANENT_COUNT=4
REPAIRABLE_AFTER_PERMANENT=4
INF=10**9
SOURCE_GROUPS={
 'AWA':('AWAL','AWAR'), 'AWC':('AWCL','AWCR'), 'ASE':('ASEL','ASER'),
 'ASH':('ASHL','ASHR'), 'ALM_AVM':('ALML','ALMR','AVM'), 'PLM':('PLML','PLMR')
}

def s(x):
    while isinstance(x,np.ndarray) and x.size==1: x=x.flat[0]
    if isinstance(x,bytes): return x.decode()
    return str(x).strip()

def load_data():
    c=loadmat(CONN,squeeze_me=True,struct_as_record=False)
    t=loadmat(TYPES,squeeze_me=True,struct_as_record=False)
    A=np.asarray(c['A_init_t_ordered'],dtype=float)
    labels=[s(x) for x in np.ravel(c['Neuron_ordered'])]
    classes=[s(x) for x in np.ravel(t['NeuronType_ordered'])]
    if A.shape[0]!=A.shape[1] or len(labels)!=A.shape[0] or len(classes)!=A.shape[0]:
        raise RuntimeError((A.shape,len(labels),len(classes)))
    return (A>0),labels,classes

def dist_to_targets(adj,targets,blocked):
    rev=[[] for _ in range(len(adj))]
    for u in range(len(adj)):
        if u in blocked: continue
        for v in np.flatnonzero(adj[u]):
            if v not in blocked: rev[v].append(u)
    d=[INF]*len(adj); q=deque()
    for x in targets:
        if x not in blocked: d[x]=0; q.append(x)
    while q:
        v=q.popleft()
        for u in rev[v]:
            if d[u]==INF: d[u]=d[v]+1; q.append(u)
    return d

def source_distance(adj,sources,targets,blocked):
    d=dist_to_targets(adj,targets,blocked)
    return min((d[x] for x in sources if x not in blocked),default=INF)

def contract_ok(adj,sources,targets,blocked):
    return source_distance(adj,sources,targets,blocked)<=H

def candidate_rank(adj,labels,classes,groups,targets):
    idx={n:i for i,n in enumerate(labels)}
    base_to_motor=dist_to_targets(adj,targets,set())
    scores=[]
    protected=set(targets)
    for xs in groups.values(): protected.update(xs)
    for v,name in enumerate(labels):
        if v in protected or 'I' not in classes[v]: continue
        if not all(contract_ok(adj,xs,targets,{v}) for xs in groups.values()): continue
        shared=0
        for xs in groups.values():
            ds=[]
            for src in xs:
                q=deque([(src,0)]); seen={src}; hit=False
                while q and not hit:
                    u,du=q.popleft()
                    if du>=H: continue
                    for w in np.flatnonzero(adj[u]):
                        if w in seen: continue
                        seen.add(w)
                        if w==v and base_to_motor[w]+du+1<=H: hit=True; break
                        q.append((w,du+1))
                if hit: shared+=1; break
        deg=int(adj[v].sum()+adj[:,v].sum())
        h=hashlib.sha256(('INSACERMO-CELEGANS-20260917|'+name).encode()).hexdigest()
        scores.append((name,v,shared,deg,h))
    scores.sort(key=lambda z:(-z[2],-z[3],z[4]))
    if len(scores)<12: raise RuntimeError(f'Only {len(scores)} eligible interneurons')
    return scores

def depth(adj,groups,targets,bundle,repairable,permanent,name_to_i):
    rep=sorted(repairable)
    perm={name_to_i[x] for x in permanent}
    rep_i={x:name_to_i[x] for x in rep}
    for k in range(len(rep)+1):
        for R in itertools.combinations(rep,k):
            blocked=set(perm)|{rep_i[x] for x in rep if x not in R}
            if all(contract_ok(adj,groups[q],targets,blocked) for q in bundle): return k
    return INF

def fmt(x): return 'INF' if x>=INF else str(x)

def main():
    adj,labels,classes=load_data(); idx={n:i for i,n in enumerate(labels)}
    missing=[n for xs in SOURCE_GROUPS.values() for n in xs if n not in idx]
    if missing: raise RuntimeError(('missing sources',missing))
    groups={k:tuple(idx[x] for x in xs) for k,xs in SOURCE_GROUPS.items()}
    targets={i for i,c in enumerate(classes) if 'M' in c}
    if not targets: raise RuntimeError('No motor neurons from class labels')
    baseline={q:source_distance(adj,xs,targets,set()) for q,xs in groups.items()}
    rank=candidate_rank(adj,labels,classes,groups,targets)
    names=[x[0] for x in rank]
    hashed=sorted(names,key=lambda n:hashlib.sha256(('INSACERMO-CELEGANS-HASH-20260917|'+n).encode()).hexdigest())
    scenarios={'BASELINE':(set(),set())}
    for k in DELETE_LEVELS: scenarios[f'SHARED_{k}_REPAIRABLE']=(set(names[:k]),set())
    scenarios[f'HASHED_{HASH_CONTROL}_REPAIRABLE']=(set(hashed[:HASH_CONTROL]),set())
    scenarios['SHARED_4_PERMANENT_PLUS_4_REPAIRABLE']=(set(names[4:8]),set(names[:4]))
    print('INSACERMO_BLIND_CELEGANS_NEURAL_REPERTOIRE_V1')
    print('NEURONS',len(labels),'CHEMICAL_EDGES',int(adj.sum()),'MOTOR_TARGETS',len(targets),'H',H)
    print('CONTRACT structural directed chemical-synapse reachability from fixed sensory groups to any motor neuron within <=4 synapses')
    print('SOURCES',' '.join(f"{k}:{','.join(SOURCE_GROUPS[k])}" for k in SOURCE_GROUPS))
    print('BASELINE_DISTANCE',' '.join(f'{q}:{fmt(d)}' for q,d in baseline.items()))
    print('ELIGIBLE_RANK',' '.join(f'{n}:{sh}:{deg}' for n,_,sh,deg,_ in rank[:20]))
    print('CAVEAT structural connectome transmission proxy only; no neural dynamics, sign, neurotransmitter, behavior, cognition, or in-vivo performance claim')
    allres={}
    keys=tuple(SOURCE_GROUPS)
    for sn,(rep,perm) in scenarios.items():
        print('SCENARIO',sn,'REPAIRABLE',len(rep),'PERMANENT',len(perm))
        sing={q:depth(adj,groups,targets,(q,),rep,perm,idx) for q in keys}
        print('SINGLETONS',' '.join(f'{q}:{fmt(sing[q])}' for q in keys))
        res={}
        for z in range(1,MAX_BUNDLE+1):
            vals=[]
            for F in itertools.combinations(keys,z):
                d=depth(adj,groups,targets,F,rep,perm,idx); res[F]=d; vals.append((F,d))
            finite=[(F,d) for F,d in vals if d<INF]; inf=[F for F,d in vals if d>=INF]
            hist=Counter(d for _,d in finite)
            print('BUNDLE_SIZE',z,'TOTAL',len(vals),'FINITE',len(finite),'INFINITE',len(inf),'DEPTH_HIST',' '.join(f'D{k}:{hist[k]}' for k in sorted(hist)))
            pos=[]; hidden=[]
            for F,d in vals:
                indiv=tuple(sing[q] for q in F)
                if d>=INF and all(x<INF for x in indiv): hidden.append((F,indiv))
                elif d<INF and all(x<INF for x in indiv) and d>max(indiv): pos.append((d-max(indiv),F,d,indiv))
            print('POSITIVE_INTERACTION_GAP',len(pos),'INFINITE_WITH_ALL_SINGLETONS_FINITE',len(hidden))
            if pos:
                g,F,d,iv=max(pos,key=lambda x:(x[0],x[1])); print('MAX_INTERACTION_GAP',g,'BUNDLE',','.join(F),'JOINT',d,'SINGLETONS',','.join(map(fmt,iv)))
        allres[sn]=res
    print('NESTED_DAMAGE_CHAIN')
    chain=['BASELINE']+[f'SHARED_{k}_REPAIRABLE' for k in DELETE_LEVELS]
    for a,b in zip(chain,chain[1:]):
        delayed=irr=unch=added=0
        for F,da in allres[a].items():
            db=allres[b][F]
            if da<INF and db>=INF: irr+=1
            elif da<INF and db<INF and db>da: delayed+=1; added+=db-da
            elif da==db: unch+=1
            else: raise AssertionError((a,b,F,da,db))
        print('TRANSFORM',a,'TO',b,'DELAYED',delayed,'NEW_IRREVERSIBLE',irr,'UNCHANGED',unch,'TOTAL_ADDED_FINITE_DEPTH',added)

if __name__=='__main__': main()
