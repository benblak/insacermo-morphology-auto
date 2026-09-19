import csv
import io
import itertools
import math
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

PHI_GOLD = (3.0 - math.sqrt(5.0)) / 2.0

def pair_duality_no_go():
    # Minimal pair obstruction F={a,b}: feasible proper nonempty subbundles,
    # infeasible full pair. Distinct simple failure-set family after removing
    # redundant supersets is uniquely {{a},{b}} up to relabeling.
    failure_sets = [frozenset({'a'}), frozenset({'b'})]
    assert all(fs for fs in failure_sets)
    # Hitting both failure sets needs {a,b}; every singleton misses one.
    full = {'a','b'}
    assert all(full & fs for fs in failure_sets)
    assert not all({'a'} & fs for fs in failure_sets)
    assert not all({'b'} & fs for fs in failure_sets)

    # Linear normalized swap-symmetric weights on a,b force equality.
    x_swap = 0.5
    return failure_sets, x_swap

def maximin_x(c):
    # c*x = (1-x)^2 -> x^2-(2+c)x+1=0; root in (0,1)
    return ((2.0 + c) - math.sqrt((2.0 + c)**2 - 4.0)) / 2.0

def pure_math_audit():
    fs, x_swap = pair_duality_no_go()
    print('PURE_DUALITY_FAILURE_SETS', ';'.join(''.join(sorted(x)) for x in fs))
    print('PURE_SWAP_SYMMETRIC_LINEAR_WEIGHT', f'{x_swap:.15f}')
    print('PURE_GOLDEN_POINT', f'{PHI_GOLD:.15f}')
    print('PURE_DUALITY_FORCES_GOLDEN', 'NO')

    for c in (0.5, 0.9, 1.0, 1.1, 2.0):
        x = maximin_x(c)
        val = min(c*x, (1-x)**2)
        print('MAXIMIN', 'C', f'{c:.6f}', 'X', f'{x:.15f}', 'VALUE', f'{val:.15f}')
    x1 = maximin_x(1.0)
    assert abs(x1 - PHI_GOLD) < 1e-14
    print('MAXIMIN_C1_EQUALS_GOLDEN', 'YES')
    print('EXTRA_AXIOM_REQUIRED', 'EQUAL_SCALE_NONLINEAR_BALANCE')

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
        depth = len(path)-1
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
                q.append((v, m2, path+(v,)))
    return None

def all_nonempty_proper_subbundles(bundle):
    n = len(bundle)
    for k in range(1,n):
        yield from itertools.combinations(bundle,k)

def is_minimal_obstruction(g,bundle):
    if shortest_covering_path(g,bundle) is not None:
        return False
    return all(shortest_covering_path(g,sub) is not None for sub in all_nonempty_proper_subbundles(bundle))

def private_witness_lengths(g,bundle):
    lens=[]
    for q in bundle:
        sub=tuple(x for x in bundle if x != q)
        path=shortest_covering_path(g,sub)
        assert path is not None
        assert q not in path
        lens.append(len(path)-1)
    return tuple(lens)

def pct(a,b):
    return 0.0 if b==0 else 100.0*a/b

def openflights_symmetry_audit():
    print('OPENFLIGHTS_ROUTES', len(rows))
    for scenario in SCENARIOS:
        g=graph_for(scenario)
        pair_lens=[]
        triple_lens=[]
        for k in (2,3):
            for bundle in itertools.combinations(REQUIRED,k):
                if is_minimal_obstruction(g,bundle):
                    lens=private_witness_lengths(g,bundle)
                    if k==2: pair_lens.append(tuple(sorted(lens)))
                    else: triple_lens.append(tuple(sorted(lens)))

        pair_equal=sum(1 for x in pair_lens if len(set(x))==1)
        pair_mad=sum(abs(x[1]-x[0]) for x in pair_lens)/len(pair_lens) if pair_lens else 0.0
        triple_equal=sum(1 for x in triple_lens if len(set(x))==1)
        triple_range=sum(x[-1]-x[0] for x in triple_lens)/len(triple_lens) if triple_lens else 0.0

        print('SCENARIO',scenario)
        print('PAIR_OBSTRUCTIONS',len(pair_lens))
        print('PAIR_EQUAL_WITNESS_LENGTHS',pair_equal,'PCT',f'{pct(pair_equal,len(pair_lens)):.6f}')
        print('PAIR_MEAN_ABS_LENGTH_DIFF',f'{pair_mad:.12f}')
        print('PAIR_LENGTH_DISTRIBUTION',dict(sorted(Counter(pair_lens).items())))
        print('TRIPLE_OBSTRUCTIONS',len(triple_lens))
        print('TRIPLE_ALL_EQUAL_WITNESS_LENGTHS',triple_equal,'PCT',f'{pct(triple_equal,len(triple_lens)):.6f}')
        print('TRIPLE_MEAN_LENGTH_RANGE',f'{triple_range:.12f}')
        print('TRIPLE_LENGTH_DISTRIBUTION',dict(sorted(Counter(triple_lens).items())))

        if pair_lens:
            print('PAIR_EQUAL_COST_STRUCTURALLY_FORCED', 'YES' if pair_equal==len(pair_lens) else 'NO')
        if triple_lens:
            print('TRIPLE_EQUAL_COST_STRUCTURALLY_FORCED', 'YES' if triple_equal==len(triple_lens) else 'NO')

if __name__ == '__main__':
    print('INSACERMO_V2_DUALITY_GOLDEN_POINT_AUDIT')
    print('PROTOCOL','FROZEN_BEFORE_RESULT')
    pure_math_audit()
    openflights_symmetry_audit()
    print('RESULT','COMPLETE')
