import csv
import io
import itertools
import urllib.request
from collections import defaultdict, deque, Counter

URL = 'https://raw.githubusercontent.com/jpatokal/openflights/master/data/routes.dat'
START = 'KEF'
REQUIRED = [
    'LHR','CDG','FRA','AMS','MAD','FCO','ATH','IST','DXB','DOH',
    'JFK','YYZ','MEX','GRU','EZE','CPT','JNB','DEL','SIN','HKG',
    'NRT','SYD','AKL','LAX','SFO'
]
DEADLINE = 3
SCENARIOS = ['BASELINE','NO_FI','NO_LHR','NO_FI_NO_LHR','KEF_SHUTDOWN']
MAX_BUNDLE = 3

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

def graph_for(scenario):
    g = defaultdict(set)
    for r in rows:
        if keep(r, scenario):
            g[r[2]].add(r[4])
    return {u: tuple(sorted(vs)) for u, vs in g.items()}

def shortest_covering_path(g, bundle, H=DEADLINE):
    """Shortest lexicographically deterministic path from START of <=H edges
    that visits every airport in bundle. Returns tuple path or None."""
    bundle = tuple(bundle)
    idx = {q: i for i, q in enumerate(bundle)}
    full = (1 << len(bundle)) - 1

    def add(mask, airport):
        i = idx.get(airport)
        return mask if i is None else (mask | (1 << i))

    start_mask = add(0, START)
    q = deque([(START, start_mask, (START,))])
    seen = {(START, start_mask): 0}

    while q:
        u, mask, path = q.popleft()
        depth = len(path) - 1
        if mask == full:
            return path
        if depth == H:
            continue
        for v in g.get(u, ()):
            m2 = add(mask, v)
            d2 = depth + 1
            state = (v, m2)
            old = seen.get(state)
            if old is None or d2 < old:
                seen[state] = d2
                q.append((v, m2, path + (v,)))
    return None

def all_nonempty_proper_subbundles(bundle):
    n = len(bundle)
    for k in range(1, n):
        yield from itertools.combinations(bundle, k)

def is_minimal_obstruction(g, bundle):
    if shortest_covering_path(g, bundle) is not None:
        return False
    return all(shortest_covering_path(g, sub) is not None
               for sub in all_nonempty_proper_subbundles(bundle))

def private_witnesses(g, bundle):
    out = {}
    for q in bundle:
        sub = tuple(x for x in bundle if x != q)
        path = shortest_covering_path(g, sub)
        assert path is not None, (bundle, q, 'missing proper-subbundle witness')
        assert q not in path, (bundle, q, path, 'witness accidentally satisfies full bundle')
        out[q] = path
    return out

print('INSACERMO_POSTFREEZE_OPENFLIGHTS_PRIVATE_WITNESS_V1')
print('PROTOCOL', 'FROZEN_BEFORE_RESULT')
print('ROUTES', len(rows))
print('START', START)
print('DEADLINE', DEADLINE)
print('TARGET_COUNT', len(REQUIRED))
print('MAX_BUNDLE', MAX_BUNDLE)

grand_total = 0
grand_by_order = Counter()

for scenario in SCENARIOS:
    g = graph_for(scenario)
    obs = []
    feasible_counts = Counter()
    total_counts = Counter()

    for k in (1, 2, 3):
        for bundle in itertools.combinations(REQUIRED, k):
            total_counts[k] += 1
            if shortest_covering_path(g, bundle) is not None:
                feasible_counts[k] += 1

    for k in (2, 3):
        for bundle in itertools.combinations(REQUIRED, k):
            if is_minimal_obstruction(g, bundle):
                witnesses = private_witnesses(g, bundle)
                obs.append((bundle, witnesses))
                grand_total += 1
                grand_by_order[k] += 1

    rank3 = [(b, w) for b, w in obs if len(b) == 3]

    print('SCENARIO', scenario)
    for k in (1, 2, 3):
        print('FEASIBILITY', 'K', k, 'SAFE', feasible_counts[k],
              'FAILED', total_counts[k] - feasible_counts[k],
              'TOTAL', total_counts[k])
    print('MINIMAL_OBSTRUCTIONS_TOTAL', len(obs))
    print('MINIMAL_OBSTRUCTIONS_ORDER2', sum(1 for b, _ in obs if len(b) == 2))
    print('MINIMAL_OBSTRUCTIONS_ORDER3', len(rank3))
    print('RANK3_PAIRWISE_COMPATIBLE_CHECK',
          'YES' if all(
              all(shortest_covering_path(g, p) is not None
                  for p in itertools.combinations(b, 2))
              for b, _ in rank3
          ) else 'NO')

    for bundle, witnesses in obs[:10]:
        print('OBSTRUCTION', 'ORDER', len(bundle), 'BUNDLE', ','.join(bundle))
        for q in bundle:
            path = witnesses[q]
            print('PRIVATE_WITNESS',
                  'DROP', q,
                  'PATHLEN', len(path)-1,
                  'PATH', '>'.join(path))

print('ALL_SCENARIOS_MINIMAL_OBSTRUCTIONS', grand_total)
print('ALL_SCENARIOS_ORDER2', grand_by_order[2])
print('ALL_SCENARIOS_ORDER3', grand_by_order[3])
print('PRIVATE_WITNESS_AUDIT', 'PASS')
print('RESULT', 'COMPLETE')
