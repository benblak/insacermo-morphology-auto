import csv
import io
import itertools
import math
import urllib.request
from collections import defaultdict, deque, Counter
from functools import lru_cache

URL = 'https://raw.githubusercontent.com/jpatokal/openflights/master/data/routes.dat'
START = 'KEF'
REQUIRED = [
    'LHR','CDG','FRA','AMS','MAD','FCO','ATH','IST','DXB','DOH',
    'JFK','YYZ','MEX','GRU','EZE','CPT','JNB','DEL','SIN','HKG',
    'NRT','SYD','AKL','LAX','SFO'
]
DEADLINE = 3
SCENARIOS = ['BASELINE','NO_FI','NO_LHR','NO_FI_NO_LHR','KEF_SHUTDOWN']
GOLD = (3.0 - math.sqrt(5.0))/2.0

text = urllib.request.urlopen(URL, timeout=60).read().decode('utf-8')
rows = list(csv.reader(io.StringIO(text)))
assert len(rows) >= 67000, len(rows)

def keep(r, scenario):
    if len(r) < 5:
        return False
    airline, src, dst = r[0], r[2], r[4]
    if src == '\\N' or dst == '\\N':
        return False
    if scenario in ('NO_FI', 'NO_FI_NO_LHR') and airline == 'FI':
        return False
    if scenario in ('NO_LHR', 'NO_FI_NO_LHR') and (src == 'LHR' or dst == 'LHR'):
        return False
    if scenario == 'KEF_SHUTDOWN' and (src == 'KEF' or dst == 'KEF'):
        return False
    return True

def graph_for_routes(scenario):
    g = defaultdict(set)
    for r in rows:
        if keep(r, scenario):
            g[r[2]].add(r[4])
    return {u: tuple(sorted(vs)) for u, vs in g.items()}

def shortest_covering_path(g, bundle, H=DEADLINE):
    bundle = tuple(bundle)
    idx = {q:i for i,q in enumerate(bundle)}
    full = (1 << len(bundle)) - 1
    def add(mask, airport):
        i = idx.get(airport)
        return mask if i is None else mask | (1 << i)
    q = deque([(START, add(0, START), 0)])
    seen = {(START, add(0, START)):0}
    while q:
        u, mask, d = q.popleft()
        if mask == full:
            return True
        if d == H:
            continue
        for v in g.get(u, ()):
            m2 = add(mask, v)
            state = (v, m2)
            if state not in seen or d+1 < seen[state]:
                seen[state] = d+1
                q.append((v, m2, d+1))
    return False

def pair_obstruction_edges(route_graph):
    singleton_ok = {q: shortest_covering_path(route_graph,(q,)) for q in REQUIRED}
    edges=[]
    for a,b in itertools.combinations(REQUIRED,2):
        if singleton_ok[a] and singleton_ok[b] and not shortest_covering_path(route_graph,(a,b)):
            edges.append((a,b))
    return singleton_ok, edges

def build_adj(edges):
    idx={q:i for i,q in enumerate(REQUIRED)}
    adj=[0]*len(REQUIRED)
    for a,b in edges:
        i,j=idx[a],idx[b]
        adj[i] |= 1<<j
        adj[j] |= 1<<i
    return idx,adj

def components(adj):
    n=len(adj)
    seen=set()
    out=[]
    for s in range(n):
        if s in seen: continue
        stack=[s]; seen.add(s); comp=[]
        while stack:
            u=stack.pop(); comp.append(u)
            nbrmask=adj[u]
            for v in range(n):
                if (nbrmask>>v)&1 and v not in seen:
                    seen.add(v); stack.append(v)
        out.append(sorted(comp))
    return out

def classify_component(comp, adj):
    s=set(comp)
    deg=[sum(1 for v in comp if (adj[u]>>v)&1) for u in comp]
    e=sum(deg)//2
    n=len(comp)
    if n==1:
        return 'ISOLATED'
    if e==n-1 and max(deg)<=2:
        return 'PATH'
    if e==n and min(deg)==2 and max(deg)==2:
        return 'CYCLE'
    if e==n-1:
        return 'TREE_BRANCHING'
    return 'CYCLIC_OR_DENSE'

def fib_path_endpoint_prob(n):
    A=[0]*(max(2,n)+1)
    A[0]=1
    A[1]=2
    for k in range(2,len(A)):
        A[k]=A[k-1]+A[k-2]
    if n==1:
        return 0.5
    return A[n-2]/A[n]

def exact_independent_set_counter(adj):
    n=len(adj)
    full=(1<<n)-1

    @lru_cache(maxsize=None)
    def Z(mask):
        if mask==0:
            return 1
        # choose present vertex with largest degree within current mask
        best=-1; bestd=-1
        m=mask
        while m:
            lsb=m & -m
            v=lsb.bit_length()-1
            d=(adj[v] & mask).bit_count()
            if d>bestd:
                bestd=d; best=v
            m-=lsb
        without = mask & ~(1<<best)
        # exclude best + include best (remove neighbors)
        return Z(without) + Z(without & ~adj[best])

    total=Z(full)
    inc=[]
    for v in range(n):
        rest = full & ~(1<<v) & ~adj[v]
        inc.append(Z(rest))
    return total, inc, Z.cache_info()

def stats(vals):
    if not vals:
        return (0.0,0.0,0.0,0.0)
    mean=sum(vals)/len(vals)
    var=sum((x-mean)**2 for x in vals)/len(vals)
    return mean,min(vals),max(vals),math.sqrt(var)

print('INSACERMO_V2_REAL_OBSTRUCTION_PATH_AUDIT')
print('PROTOCOL','FROZEN_BEFORE_RESULT')
print('GOLDEN_REFERENCE',f'{GOLD:.15f}')
print('ROUTES',len(rows))

for scenario in SCENARIOS:
    rg=graph_for_routes(scenario)
    singleton_ok, edges=pair_obstruction_edges(rg)
    idx,adj=build_adj(edges)
    comps=components(adj)
    degs=[a.bit_count() for a in adj]
    density=(2*len(edges))/(len(REQUIRED)*(len(REQUIRED)-1))
    print('SCENARIO',scenario)
    print('PAIR_OBSTRUCTION_VERTICES',len(REQUIRED),'EDGES',len(edges),'DENSITY',f'{density:.12f}')
    print('SINGLETON_FEASIBLE',sum(singleton_ok.values()),'OF',len(REQUIRED))
    print('DEGREE_DISTRIBUTION',dict(sorted(Counter(degs).items())))
    print('COMPONENT_SIZES',sorted([len(c) for c in comps],reverse=True))
    class_counts=Counter()
    for ci,comp in enumerate(sorted(comps,key=lambda c:(-len(c),[REQUIRED[i] for i in c]))):
        cls=classify_component(comp,adj); class_counts[cls]+=1
        names=[REQUIRED[i] for i in comp]
        # edge count inside comp
        e=sum(sum(1 for v in comp if (adj[u]>>v)&1) for u in comp)//2
        print('COMPONENT',ci,'CLASS',cls,'N',len(comp),'E',e,'VERTICES',','.join(names))
        if cls=='PATH' and len(comp)>=2:
            p=fib_path_endpoint_prob(len(comp))
            print('PATH_ENDPOINT_THEORY','N',len(comp),'P',f'{p:.15f}','ERR_TO_GOLDEN',f'{p-GOLD:.15e}')
    print('COMPONENT_CLASS_COUNTS',dict(sorted(class_counts.items())))

    total, inc, ci = exact_independent_set_counter(adj)
    marg=[x/total for x in inc]
    mean,mn,mx,sd=stats(marg)
    closest=min(range(len(REQUIRED)),key=lambda i:abs(marg[i]-GOLD))
    within005=sum(abs(x-GOLD)<=0.005 for x in marg)
    within01=sum(abs(x-GOLD)<=0.01 for x in marg)
    print('INDEPENDENT_SETS_TOTAL',total)
    print('MARGINAL_MEAN',f'{mean:.15f}','MIN',f'{mn:.15f}','MAX',f'{mx:.15f}','SD',f'{sd:.15f}')
    print('WITHIN_0_005_OF_GOLDEN',within005,'OF',len(marg))
    print('WITHIN_0_01_OF_GOLDEN',within01,'OF',len(marg))
    print('CLOSEST_VERTEX',REQUIRED[closest],'P',f'{marg[closest]:.15f}','ABS_ERR',f'{abs(marg[closest]-GOLD):.15e}')
    for i,q in enumerate(REQUIRED):
        print('VERTEX_MARGINAL',q,'DEG',degs[i],'P',f'{marg[i]:.15f}','ERR',f'{marg[i]-GOLD:.15e}')
    print('DP_CACHE',ci)

print('RESULT','COMPLETE')
