import hashlib
import itertools
import os
import re
from collections import Counter, defaultdict, deque

from z3 import And, Bool, Not, Or, Solver, sat

MODEL_PATH = os.environ.get("INSACERMO_TCELL_BNET", "/tmp/tcell_diff.bnet")
DELETE_LEVELS = (3, 6, 9)
HASH_CONTROL = 6
PERMANENT_COUNT = 3
REPAIRABLE_AFTER_PERMANENT = 3
INF = 10**9

# Fixed-before-result phenotype contracts.
# These marker definitions follow standard Th0/Th1/Th2 logical-model practice:
# Th0 lacks the two lineage TFs and their hallmark cytokines;
# Th1 expresses Tbet + IFNg with GATA3 off;
# Th2 expresses GATA3 + IL4 with Tbet off.
PHENOTYPES = {
    "Th0": {"Tbet": False, "GATA3": False, "IFNg": False, "IL4": False},
    "Th1": {"Tbet": True, "GATA3": False, "IFNg": True},
    "Th2": {"GATA3": True, "Tbet": False, "IL4": True},
}
PROTECTED = {"Tbet", "GATA3", "IFNg", "IL4"}


def parse_bnet(path):
    rules = {}
    with open(path, "r", encoding="utf-8") as f:
        for raw in f:
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            lhs, rhs = line.split(",", 1)
            rules[lhs.strip()] = rhs.strip()
    if not rules:
        raise RuntimeError("No Boolean rules loaded")
    names = set(rules)
    for rhs in rules.values():
        names.update(re.findall(r"\b[A-Za-z_][A-Za-z0-9_]*\b", rhs))
    return rules, sorted(names)


def zexpr(rhs, var):
    # bnet operators -> Python operators overloaded by z3 BoolRef.
    expr = rhs.replace("!", "~")
    return eval(expr, {"__builtins__": {}}, var)


def make_solver(rules, names, knocked):
    var = {n: Bool(n) for n in names}
    s = Solver()
    for lhs, rhs in rules.items():
        if lhs in knocked:
            s.add(var[lhs] == False)
        else:
            s.add(var[lhs] == zexpr(rhs, var))
    return s, var


def phenotype_exists(rules, names, knocked, phenotype):
    s, var = make_solver(rules, names, knocked)
    for n, val in PHENOTYPES[phenotype].items():
        s.add(var[n] == val)
    return s.check() == sat


def phenotype_witness(rules, names, knocked, phenotype):
    s, var = make_solver(rules, names, knocked)
    for n, val in PHENOTYPES[phenotype].items():
        s.add(var[n] == val)
    if s.check() != sat:
        return None
    m = s.model()
    return {n: bool(m.eval(var[n], model_completion=True)) for n in names}


def dependency_graph(rules):
    out = defaultdict(set)
    indeg = Counter()
    for target, rhs in rules.items():
        deps = set(re.findall(r"\b[A-Za-z_][A-Za-z0-9_]*\b", rhs))
        for d in deps:
            out[d].add(target)
            indeg[target] += 1
    return out, indeg


def reaches_any(out, source, targets):
    q = deque([source])
    seen = {source}
    while q:
        u = q.popleft()
        if u != source and u in targets:
            return True
        for v in out.get(u, ()):
            if v not in seen:
                seen.add(v)
                q.append(v)
    return False


def rank_candidates(rules, names):
    out, indeg = dependency_graph(rules)
    phenotype_targets = {
        p: set(markers)
        for p, markers in PHENOTYPES.items()
    }
    eligible = []
    for node in sorted(rules):
        if node in PROTECTED:
            continue
        # A destruction candidate is individually silent for the full declared
        # fate repertoire: each phenotype still exists after this one knockout.
        if not all(phenotype_exists(rules, names, {node}, p) for p in PHENOTYPES):
            continue
        shared = sum(reaches_any(out, node, t) for t in phenotype_targets.values())
        degree = len(out.get(node, ())) + indeg[node]
        h = hashlib.sha256(("INSACERMO-TCELL-FATE-20260917|" + node).encode()).hexdigest()
        eligible.append((node, shared, degree, h))
    eligible.sort(key=lambda x: (-x[1], -x[2], x[3]))
    if len(eligible) < max(DELETE_LEVELS):
        raise RuntimeError(f"Only {len(eligible)} individually-silent candidates; need {max(DELETE_LEVELS)}")
    return eligible


def repertoire_depth(rules, names, bundle, repairable, permanent, cache):
    rep = sorted(repairable)
    for k in range(len(rep) + 1):
        for restored in itertools.combinations(rep, k):
            knocked = frozenset(permanent | (set(rep) - set(restored)))
            ok = True
            for p in bundle:
                key = (knocked, p)
                if key not in cache:
                    cache[key] = phenotype_exists(rules, names, set(knocked), p)
                if not cache[key]:
                    ok = False
                    break
            if ok:
                return k
    return INF


def fmt(d):
    return "INF" if d >= INF else str(int(d))


def main():
    rules, names = parse_bnet(MODEL_PATH)
    undefined_inputs = sorted(set(names) - set(rules))

    print("INSACERMO_BLIND_TCELL_FATE_PORTFOLIO_V1")
    print("MODEL Cell-Collective-derived T-cell differentiation Boolean network")
    print("RULED_NODES", len(rules), "TOTAL_BOOLEAN_VARIABLES", len(names))
    print("FREE_ENVIRONMENT_INPUTS", ",".join(undefined_inputs))
    print("SEMANTICS a fate remains available iff the perturbed Boolean network admits at least one fixed point matching its predeclared phenotype markers; free environment inputs may differ between fates")
    print("PHENOTYPES", " | ".join(f"{p}:" + ",".join(f"{k}={int(v)}" for k, v in m.items()) for p, m in PHENOTYPES.items()))
    print("CAVEAT logical fixed-point repertoire model only; not a patient, clinical, causal, quantitative expression, population-dynamics, or in-vivo differentiation claim")

    for p in PHENOTYPES:
        w = phenotype_witness(rules, names, set(), p)
        if w is None:
            raise RuntimeError(f"Baseline phenotype absent: {p}")
        active = sorted(n for n, v in w.items() if v)
        print("BASELINE_WITNESS", p, "ACTIVE", ",".join(active))

    ranked = rank_candidates(rules, names)
    ordered = [x[0] for x in ranked]
    print("ELIGIBLE", len(ranked))
    print("ELIGIBLE_RANK", " ".join(f"{n}:{shared}:{deg}" for n, shared, deg, _ in ranked))

    hashed = sorted(ordered, key=lambda n: hashlib.sha256(("INSACERMO-TCELL-HASH-20260917|" + n).encode()).hexdigest())
    scenarios = {"BASELINE": (set(), set())}
    for k in DELETE_LEVELS:
        scenarios[f"SHARED_{k}_REPAIRABLE"] = (set(ordered[:k]), set())
    scenarios[f"HASHED_{HASH_CONTROL}_REPAIRABLE"] = (set(hashed[:HASH_CONTROL]), set())
    scenarios[f"SHARED_{PERMANENT_COUNT}_PERMANENT_PLUS_{REPAIRABLE_AFTER_PERMANENT}_REPAIRABLE"] = (
        set(ordered[PERMANENT_COUNT:PERMANENT_COUNT + REPAIRABLE_AFTER_PERMANENT]),
        set(ordered[:PERMANENT_COUNT]),
    )

    phen = tuple(PHENOTYPES)
    all_results = {}
    cache = {}

    for sname, (repairable, permanent) in scenarios.items():
        print("SCENARIO", sname, "REPAIRABLE", len(repairable), "PERMANENT", len(permanent))
        singleton = {
            p: repertoire_depth(rules, names, (p,), repairable, permanent, cache)
            for p in phen
        }
        print("SINGLETONS", " ".join(f"{p}:{fmt(singleton[p])}" for p in phen))
        results = {}
        for size in (1, 2, 3):
            vals = []
            for F in itertools.combinations(phen, size):
                d = repertoire_depth(rules, names, F, repairable, permanent, cache)
                results[F] = d
                vals.append((F, d))
            finite = [(F, d) for F, d in vals if d < INF]
            infinite = [(F, d) for F, d in vals if d >= INF]
            hist = Counter(d for _, d in finite)
            print("BUNDLE_SIZE", size, "TOTAL", len(vals), "FINITE", len(finite), "INFINITE", len(infinite), "DEPTH_HIST", " ".join(f"D{k}:{hist[k]}" for k in sorted(hist)))
            positive = []
            hidden_inf = []
            for F, d in vals:
                indiv = tuple(singleton[p] for p in F)
                if d >= INF and all(x < INF for x in indiv):
                    hidden_inf.append((F, indiv))
                elif d < INF and all(x < INF for x in indiv) and d > max(indiv):
                    positive.append((d - max(indiv), F, d, indiv))
            print("POSITIVE_INTERACTION_GAP", len(positive), "INFINITE_WITH_ALL_SINGLETONS_FINITE", len(hidden_inf))
            if positive:
                gap, F, d, indiv = max(positive, key=lambda x: (x[0], x[1]))
                print("MAX_INTERACTION_GAP", gap, "BUNDLE", ",".join(F), "JOINT", fmt(d), "SINGLETONS", ",".join(map(fmt, indiv)))
        all_results[sname] = results

    print("NESTED_DAMAGE_CHAIN")
    chain = ["BASELINE"] + [f"SHARED_{k}_REPAIRABLE" for k in DELETE_LEVELS]
    for a, b in zip(chain, chain[1:]):
        delayed = irreversible = unchanged = finite_added = 0
        for F, da in all_results[a].items():
            db = all_results[b][F]
            if da < INF and db >= INF:
                irreversible += 1
            elif da < INF and db < INF and db > da:
                delayed += 1
                finite_added += db - da
            elif da == db:
                unchanged += 1
            else:
                raise AssertionError(("destruction made repertoire easier", a, b, F, da, db))
        print("TRANSFORM", a, "TO", b, "DELAYED", delayed, "NEW_IRREVERSIBLE", irreversible, "UNCHANGED", unchanged, "TOTAL_ADDED_FINITE_DEPTH", finite_added)


if __name__ == "__main__":
    main()
