import csv
import io
import itertools
import urllib.request
from collections import defaultdict, deque, Counter

URL = 'https://raw.githubusercontent.com/jpatokal/openflights/master/data/routes.dat'
START = 'KEF'
REQUIRED = ['LHR','CDG','FRA','AMS','MAD','FCO','ATH','IST','DXB','DOH','JFK','YYZ','MEX','GRU','EZE','CPT','JNB','DEL','SIN','HKG','NRT','SYD','AKL','LAX','SFO']
DEADLINE = 3
MAX_BUNDLE = 3
SCENARIOS = ['BASELINE','NO_FI','NO_LHR','NO_FI_NO_LHR','KEF_SHUTDOWN']

text = urllib.request.urlopen(URL, timeout=60).read().decode('utf-8')
rows = list(csv.reader(io.StringIO(text)))
assert len(rows) >= 67000, len(rows)


def keep(r, scenario):
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
        if len(r) >= 5 and keep(r, scenario):
            g[r[2]].add(r[4])
    return g


def bfs(g, start):
    d = {start: 0}
    q = deque([start])
    while q:
        u = q.popleft()
        for v in g.get(u, ()):
            if v not in d:
                d[v] = d[u] + 1
                q.append(v)
    return d


def joint_depth(pairwise, bundle):
    best = None
    for perm in itertools.permutations(bundle):
        total = 0
        cur = START
        ok = True
        for nxt in perm:
            dv = pairwise[cur].get(nxt)
            if dv is None:
                ok = False
                break
            total += dv
            cur = nxt
        if ok and (best is None or total < best):
            best = total
    return best


def fmt_depth(d):
    return 'INF' if d is None else str(d)


print('INSACERMO_BLIND_OPENFLIGHTS_JOINT_DEPTH_SPECTRUM_V1')
print('ROUTES', len(rows))
print('START', START)
print('REQUIRED', len(REQUIRED), ' '.join(REQUIRED))
print('DEADLINE', DEADLINE)
print('MAX_BUNDLE', MAX_BUNDLE)

for scenario in SCENARIOS:
    g = graph_for(scenario)
    sources = [START] + REQUIRED
    pairwise = {s: bfs(g, s) for s in sources}

    singleton_depth = {q: pairwise[START].get(q) for q in REQUIRED}

    print('SCENARIO', scenario)
    print('SINGLETONS', ' '.join(f'{q}:{fmt_depth(singleton_depth[q])}' for q in REQUIRED))

    for k in range(1, MAX_BUNDLE + 1):
        hist = Counter()
        total_bundles = 0
        finite = 0
        infinite = 0
        deadline_safe = 0
        individual_safe_joint_unsafe = 0
        positive_gap = 0
        max_gap = None
        max_gap_bundle = None
        max_depth = None
        max_depth_bundle = None

        for bundle in itertools.combinations(REQUIRED, k):
            total_bundles += 1
            d = joint_depth(pairwise, bundle)
            hist['INF' if d is None else d] += 1
            if d is None:
                infinite += 1
            else:
                finite += 1
                if d <= DEADLINE:
                    deadline_safe += 1
                if max_depth is None or d > max_depth:
                    max_depth = d
                    max_depth_bundle = bundle

            single_vals = [singleton_depth[q] for q in bundle]
            all_single_finite = all(v is not None for v in single_vals)
            all_single_safe = all(v is not None and v <= DEADLINE for v in single_vals)

            if all_single_safe and (d is None or d > DEADLINE):
                individual_safe_joint_unsafe += 1

            if all_single_finite and d is not None:
                gap = d - max(single_vals)
                if gap > 0:
                    positive_gap += 1
                if max_gap is None or gap > max_gap:
                    max_gap = gap
                    max_gap_bundle = bundle

        ordered_hist = []
        for key in sorted((x for x in hist if x != 'INF')):
            ordered_hist.append(f'D{key}:{hist[key]}')
        if hist.get('INF', 0):
            ordered_hist.append(f'INF:{hist["INF"]}')

        print('BUNDLE_SIZE', k)
        print('TOTAL', total_bundles, 'FINITE', finite, 'INFINITE', infinite, 'SAFE_H3', deadline_safe)
        print('DEPTH_HIST', ' '.join(ordered_hist))
        print('INDIVIDUAL_SAFE_JOINT_UNSAFE_H3', individual_safe_joint_unsafe)
        print('POSITIVE_INTERACTION_GAP', positive_gap)
        print('MAX_INTERACTION_GAP', 'NA' if max_gap is None else max_gap,
              'BUNDLE', 'NA' if max_gap_bundle is None else ','.join(max_gap_bundle))
        print('MAX_FINITE_DEPTH', 'NA' if max_depth is None else max_depth,
              'BUNDLE', 'NA' if max_depth_bundle is None else ','.join(max_depth_bundle))

    # Explicit deadline-level witnesses, chosen deterministically by lexicographic order.
    witnesses = []
    for k in (2, 3):
        for bundle in itertools.combinations(REQUIRED, k):
            d = joint_depth(pairwise, bundle)
            single_vals = [singleton_depth[q] for q in bundle]
            if all(v is not None and v <= DEADLINE for v in single_vals) and (d is None or d > DEADLINE):
                witnesses.append((bundle, d, tuple(single_vals)))
    print('FIRST_JOINT_UNSAFE_WITNESSES')
    for bundle, d, singles in witnesses[:10]:
        print('WITNESS', ','.join(bundle), 'JOINT', fmt_depth(d),
              'SINGLETONS', ','.join(fmt_depth(v) for v in singles))
