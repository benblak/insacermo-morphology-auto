import csv, io, urllib.request
from collections import defaultdict, deque

URL='https://raw.githubusercontent.com/jpatokal/openflights/master/data/routes.dat'
START='KEF'
REQUIRED=['LHR','CDG','FRA','AMS','MAD','FCO','ATH','IST','DXB','DOH','JFK','YYZ','MEX','GRU','EZE','CPT','JNB','DEL','SIN','HKG','NRT','SYD','AKL','LAX','SFO']
DEADLINE=3

text=urllib.request.urlopen(URL,timeout=60).read().decode('utf-8')
rows=list(csv.reader(io.StringIO(text)))
assert len(rows) >= 67000, len(rows)

# fixed-before-result scenarios
SCENARIOS=['BASELINE','NO_FI','NO_LHR','NO_FI_NO_LHR','KEF_SHUTDOWN']

def keep(r,scenario):
    airline,src,dst=r[0],r[2],r[4]
    if src=='\\N' or dst=='\\N': return False
    if scenario in ('NO_FI','NO_FI_NO_LHR') and airline=='FI': return False
    if scenario in ('NO_LHR','NO_FI_NO_LHR') and (src=='LHR' or dst=='LHR'): return False
    if scenario=='KEF_SHUTDOWN' and (src=='KEF' or dst=='KEF'): return False
    return True

def graph_for(scenario):
    g=defaultdict(set)
    for r in rows:
        if len(r)>=5 and keep(r,scenario): g[r[2]].add(r[4])
    return g

def distances(g,start):
    d={start:0}; q=deque([start])
    while q:
        u=q.popleft()
        for v in g.get(u,()):
            if v not in d:
                d[v]=d[u]+1; q.append(v)
    return d

print('INSACERMO_BLIND_OPENFLIGHTS_TEMPORAL_V1')
print('ROUTES',len(rows))
print('START',START)
print('REQUIRED',len(REQUIRED),' '.join(REQUIRED))
print('DEADLINE',DEADLINE)
for scenario in SCENARIOS:
    g=graph_for(scenario); d=distances(g,START)
    vals={x:d.get(x) for x in REQUIRED}
    act=sum(1 for x,v in vals.items() if v==1)
    recover=sum(1 for x,v in vals.items() if v is not None and v>1)
    refuse=sum(1 for x,v in vals.items() if v is None)
    debt={H:sum(1 for v in vals.values() if v is None or v>H) for H in [1,2,3,4,5]}
    late=sum(1 for v in vals.values() if v is not None and v>DEADLINE)
    irreversible=refuse
    safe=all(v is not None and v<=DEADLINE for v in vals.values())
    print('SCENARIO',scenario)
    print('ACT_DIRECT',act,'RECOVER_MULTI',recover,'REFUSE',refuse)
    print('TEMPORAL_DEBT',' '.join(f'H{H}:{debt[H]}' for H in [1,2,3,4,5]))
    print('LATE_DEBT_H3',late,'IRREVERSIBLE_DEBT',irreversible,'SAFE_WITHIN_H3',safe)
    for x in REQUIRED:
        print('DEST',x,'D',vals[x] if vals[x] is not None else 'INF')
