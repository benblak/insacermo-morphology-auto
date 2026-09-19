import itertools

def all_subsets(items):
    items = tuple(items)
    for r in range(len(items) + 1):
        for c in itertools.combinations(items, r):
            yield frozenset(c)

def union_all(family):
    out = set()
    for s in family:
        out.update(s)
    return frozenset(out)

# ---------------------------------------------------------------------------
# A. Single-required-set repair model
# Each future q has one mandatory repair signature R(q).
# Unit-cost bundle depth is |union R(q)|.
# ---------------------------------------------------------------------------
U5 = tuple(range(5))
subs5 = list(all_subsets(U5))
pair_checks = 0
for A in subs5:
    for B in subs5:
        eps = len(A | B) - max(len(A), len(B))
        rhs = min(len(A - B), len(B - A))
        assert eps == rhs
        assert (eps == 0) == (A <= B or B <= A)
        pair_checks += 1

U4 = tuple(range(4))
subs4 = list(all_subsets(U4))
family_checks = 0
chain_families = 0
for r in range(1, 5):
    for fam in itertools.combinations(subs4, r):
        pair_zero = all(
            len(A | B) == max(len(A), len(B))
            for A, B in itertools.combinations(fam, 2)
        )
        if pair_zero:
            assert all(
                A <= B or B <= A
                for A, B in itertools.combinations(fam, 2)
            )
            assert len(union_all(fam)) == max(len(A) for A in fam)
            chain_families += 1
        family_checks += 1

print("SINGLE_REQUIRED_SET_PAIR_CHECKS", pair_checks)
print("SINGLE_REQUIRED_SET_FAMILY_CHECKS", family_checks)
print("CHAIN_COLLAPSE_FAMILIES", chain_families)
print("CHAIN_COLLAPSE_VERIFIED YES")

# ---------------------------------------------------------------------------
# B. Alternative-plan model
# k actions and k futures. Future i accepts any singleton action except i.
# Every proper nonempty future bundle has a common cost-1 plan, while the full
# k-bundle needs cost 2. Hence a minimal obstruction can have arbitrary order.
# ---------------------------------------------------------------------------

def good(k, future, plan):
    allowed = set(range(k)) - {future}
    return bool(set(plan) & allowed)

def min_depth(k, bundle):
    actions = tuple(range(k))
    for h in range(k + 1):
        for plan in itertools.combinations(actions, h):
            if all(good(k, q, plan) for q in bundle):
                return h
    return None

for k in range(3, 13):
    futures = tuple(range(k))
    full_depth = min_depth(k, futures)
    assert full_depth == 2

    proper_checked = 0
    for r in range(1, k):
        for bundle in itertools.combinations(futures, r):
            assert min_depth(k, bundle) == 1
            proper_checked += 1

    print(
        "ARBITRARY_ORDER_OBSTRUCTION",
        "ORDER", k,
        "PROPER_BUNDLES_CHECKED", proper_checked,
        "PROPER_DEPTH", 1,
        "FULL_DEPTH", full_depth,
        "BOUNDARY_SPHERE_DIM", k - 2,
    )

# ---------------------------------------------------------------------------
# C. Exact nerve identity for the k=3 witness at budgets H=0,1,2.
# A_H(q) is the set of complete repair plans of cost <= H that satisfy q.
# A bundle is safe iff the corresponding A_H(q) have nonempty intersection.
# ---------------------------------------------------------------------------

def plans_upto(k, H):
    out = []
    for h in range(H + 1):
        out.extend(frozenset(c) for c in itertools.combinations(range(k), h))
    return out

def safe_by_common_plan(k, bundle, H):
    return any(
        all(good(k, q, p) for q in bundle)
        for p in plans_upto(k, H)
    )

def safe_by_nerve(k, bundle, H):
    plan_universe = plans_upto(k, H)
    feasible_sets = []
    for q in bundle:
        feasible_sets.append({
            p for p in plan_universe if good(k, q, p)
        })
    if not feasible_sets:
        return True
    inter = set(feasible_sets[0])
    for s in feasible_sets[1:]:
        inter &= s
    return bool(inter)

k = 3
nonempty_bundles = [
    frozenset(c)
    for r in range(1, k + 1)
    for c in itertools.combinations(range(k), r)
]

for H in range(3):
    safe = 0
    for bundle in nonempty_bundles:
        a = safe_by_common_plan(k, bundle, H)
        b = safe_by_nerve(k, bundle, H)
        assert a == b
        safe += int(a)
    print(
        "NERVE_FILTRATION",
        "H", H,
        "SAFE", safe,
        "FAILED", len(nonempty_bundles) - safe,
    )

assert sum(safe_by_common_plan(3, b, 0) for b in nonempty_bundles) == 0
assert sum(safe_by_common_plan(3, b, 1) for b in nonempty_bundles) == 6
assert sum(safe_by_common_plan(3, b, 2) for b in nonempty_bundles) == 7

print("REPAIR_NERVE_REPRESENTATION_VERIFIED YES")
print("ARBITRARY_ORDER_FUTURE_OBSTRUCTION_VERIFIED K3_TO_K12")
print("RESULT COMPLETE")
