import hashlib
import itertools
import os
import re
from collections import Counter, defaultdict, deque

from z3 import And, Bool, If, Not, Or, PbLe, Solver, Sum, sat

MODEL_PATH = os.environ.get("INSACERMO_TCELL_BNET", "/tmp/tcell_diff.bnet")
PATH_HORIZON = 6
DELETE_LEVELS = (3, 6, 9)
HASH_CONTROL = 6
PERMANENT_COUNT = 3
REPAIRABLE_AFTER_PERMANENT = 3
INF = 10**9

# Fixed-before-result fate markers, unchanged from V1.
PHENOTYPES = {
    "Th0": {"Tbet": False, "GATA3": False, "IFNg": False, "IL4": False},
    "Th1": {"Tbet": True, "GATA3": False, "IFNg": True},
    "Th2": {"GATA3": True, "Tbet": False, "IL4": True},
}
# The common precursor is constrained only on lineage/hallmark markers;
# all other regulated nodes are existential but shared across branches.
PRECURSOR_MARKERS = {"Tbet": False, "GATA3": False, "IFNg": False, "IL4": False}
PROTECTED = set(PRECURSOR_MARKERS)


def parse_bnet(path):
    rules = {}
    with open(path, "r", encoding="utf-8") as f:
        for raw in f:
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            lhs, rhs = line.split(",", 1)
            rules[lhs.strip()] = rhs.strip()
    names = set(rules)
    for rhs in rules.values():
        names.update(re.findall(r"\b[A-Za-z_][A-Za-z0-9_]*\b", rhs))
    if not rules:
        raise RuntimeError("No Boolean rules loaded")
    return rules, sorted(names)


def expr(rhs, var):
    return eval(rhs.replace("!", "~"), {"__builtins__": {}}, var)


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


def build_branching_solver(rules, names, bundle, repairable, permanent):
    ruled = tuple(sorted(rules))
    inputs = tuple(sorted(set(names) - set(rules)))
    repairable = set(repairable)
    permanent = set(permanent)

    s = Solver()
    env = {n: Bool(f"env__{n}") for n in inputs}
    start = {n: Bool(f"start__{n}") for n in ruled}
    restore = {n: Bool(f"restore__{n}") for n in sorted(repairable)}

    for n, val in PRECURSOR_MARKERS.items():
        if n in start:
            s.add(start[n] == val)

    def active(n):
        if n in permanent:
            return False
        if n in restore:
            return restore[n]
        return True

    for fate in bundle:
        x = []
        for t in range(PATH_HORIZON + 1):
            xt = {n: Bool(f"x__{fate}__{t}__{n}") for n in names}
            x.append(xt)
            for n in inputs:
                s.add(xt[n] == env[n])
            for n in permanent:
                if n in xt:
                    s.add(Not(xt[n]))
            for n in repairable:
                if n in xt:
                    s.add(Or(restore[n], Not(xt[n])))

        # All fate branches begin from exactly the same precursor state/environment.
        for n in ruled:
            if n in permanent:
                s.add(Not(x[0][n]))
            elif n in restore:
                s.add(x[0][n] == And(restore[n], start[n]))
            else:
                s.add(x[0][n] == start[n])

        # Bounded asynchronous dynamics: at each step either stutter or update
        # exactly one regulated node according to its Boolean rule.
        for t in range(PATH_HORIZON):
            current = x[t]
            nxt = x[t + 1]
            choices = [And(*[nxt[n] == current[n] for n in ruled])]
            for chosen in ruled:
                clauses = []
                for n in ruled:
                    if n != chosen:
                        clauses.append(nxt[n] == current[n])
                    else:
                        rhs = expr(rules[n], current)
                        a = active(n)
                        if a is False:
                            clauses.append(Not(nxt[n]))
                        elif a is True:
                            clauses.append(nxt[n] == rhs)
                        else:
                            clauses.append(nxt[n] == And(a, rhs))
                choices.append(And(*clauses))
            s.add(Or(*choices))

        final = x[-1]
        # Target must be an actual fixed point of the perturbed network.
        for n in ruled:
            rhs = expr(rules[n], final)
            a = active(n)
            if a is False:
                s.add(Not(final[n]))
            elif a is True:
                s.add(final[n] == rhs)
            else:
                s.add(final[n] == And(a, rhs))
        for n, val in PHENOTYPES[fate].items():
            s.add(final[n] == val)

    return s, restore, env, start


def recovery_depth(rules, names, bundle, repairable, permanent, witness=False):
    s, restore, env, start = build_branching_solver(rules, names, bundle, repairable, permanent)
    rvars = list(restore.values())
    if not rvars:
        if s.check() != sat:
            return (INF, None) if witness else INF
        if witness:
            m = s.model()
            return 0, {
                "environment": {n: bool(m.eval(v, model_completion=True)) for n, v in env.items()},
                "precursor_active": sorted(n for n, v in start.items() if bool(m.eval(v, model_completion=True))),
            }
        return 0
    for k in range(len(rvars) + 1):
        s.push()
        s.add(PbLe([(v, 1) for v in rvars], k))
        if s.check() == sat:
            if witness:
                m = s.model()
                ans = {
                    "environment": {n: bool(m.eval(v, model_completion=True)) for n, v in env.items()},
                    "precursor_active": sorted(n for n, v in start.items() if bool(m.eval(v, model_completion=True))),
                    "restored": sorted(n for n, v in restore.items() if bool(m.eval(v, model_completion=True))),
                }
                s.pop()
                return k, ans
            s.pop()
            return k
        s.pop()
    return (INF, None) if witness else INF


def rank_candidates(rules, names):
    out, indeg = dependency_graph(rules)
    targets = {p: set(markers) for p, markers in PHENOTYPES.items()}
    eligible = []
    for node in sorted(rules):
        if node in PROTECTED:
            continue
        # Eligibility is singleton-only: one knockout must leave EACH fate
        # individually branchable from some precursor/environment. Pair/triple
        # joint feasibility is deliberately not consulted here.
        if not all(recovery_depth(rules, names, (p,), set(), {node}) == 0 for p in PHENOTYPES):
            continue
        shared = sum(reaches_any(out, node, t) for t in targets.values())
        degree = len(out.get(node, ())) + indeg[node]
        h = hashlib.sha256(("INSACERMO-TCELL-COMMON-BRANCHING-20260917|" + node).encode()).hexdigest()
        eligible.append((node, shared, degree, h))
    eligible.sort(key=lambda x: (-x[1], -x[2], x[3]))
    if len(eligible) < max(DELETE_LEVELS):
        raise RuntimeError(f"Only {len(eligible)} singleton-silent candidates; need {max(DELETE_LEVELS)}")
    return eligible


def fmt(d):
    return "INF" if d >= INF else str(int(d))


def main():
    rules, names = parse_bnet(MODEL_PATH)
    inputs = sorted(set(names) - set(rules))
    phen = tuple(PHENOTYPES)

    print("INSACERMO_BLIND_TCELL_COMMON_BRANCHING_V2")
    print("RULED_NODES", len(rules), "TOTAL_BOOLEAN_VARIABLES", len(names))
    print("FREE_ENVIRONMENT_INPUTS", ",".join(inputs))
    print("PATH_HORIZON", PATH_HORIZON)
    print("SEMANTICS one shared precursor state and one shared environment per bundle; separate bounded asynchronous branches may lead to distinct phenotype fixed points")
    print("PRECURSOR_CONSTRAINT", ",".join(f"{k}={int(v)}" for k, v in PRECURSOR_MARKERS.items()))
    print("PHENOTYPES", " | ".join(f"{p}:" + ",".join(f"{k}={int(v)}" for k, v in m.items()) for p, m in PHENOTYPES.items()))
    print("CAVEAT existential logical precursor and bounded asynchronous Boolean dynamics only; no claim of biological transition probabilities, timing, patient outcome, causality, or in-vivo differentiation")

    for size in (1, 2, 3):
        for F in itertools.combinations(phen, size):
            d, w = recovery_depth(rules, names, F, set(), set(), witness=True)
            print("BASELINE_BUNDLE", ",".join(F), "DEPTH", fmt(d), "ENV", "NA" if w is None else ",".join(f"{k}={int(v)}" for k, v in sorted(w["environment"].items())), "PRECURSOR_ACTIVE", "NA" if w is None else ",".join(w["precursor_active"]))

    ranked = rank_candidates(rules, names)
    ordered = [x[0] for x in ranked]
    print("ELIGIBLE", len(ranked))
    print("ELIGIBLE_RANK", " ".join(f"{n}:{shared}:{deg}" for n, shared, deg, _ in ranked))

    hashed = sorted(ordered, key=lambda n: hashlib.sha256(("INSACERMO-TCELL-COMMON-HASH-20260917|" + n).encode()).hexdigest())
    scenarios = {"BASELINE": (set(), set())}
    for k in DELETE_LEVELS:
        scenarios[f"SHARED_{k}_REPAIRABLE"] = (set(ordered[:k]), set())
    scenarios[f"HASHED_{HASH_CONTROL}_REPAIRABLE"] = (set(hashed[:HASH_CONTROL]), set())
    scenarios["SHARED_3_PERMANENT_PLUS_3_REPAIRABLE"] = (set(ordered[3:6]), set(ordered[:3]))

    all_results = {}
    for sname, (repairable, permanent) in scenarios.items():
        print("SCENARIO", sname, "REPAIRABLE", len(repairable), "PERMANENT", len(permanent))
        results = {}
        singletons = {}
        for size in (1, 2, 3):
            vals = []
            for F in itertools.combinations(phen, size):
                d = recovery_depth(rules, names, F, repairable, permanent)
                results[F] = d
                vals.append((F, d))
                if size == 1:
                    singletons[F[0]] = d
            finite = [(F, d) for F, d in vals if d < INF]
            infinite = [(F, d) for F, d in vals if d >= INF]
            hist = Counter(d for _, d in finite)
            print("BUNDLE_SIZE", size, "TOTAL", len(vals), "FINITE", len(finite), "INFINITE", len(infinite), "DEPTH_HIST", " ".join(f"D{k}:{hist[k]}" for k in sorted(hist)))
            positive = []
            hidden_inf = []
            if size > 1:
                for F, d in vals:
                    indiv = tuple(singletons[p] for p in F)
                    if d >= INF and all(x < INF for x in indiv):
                        hidden_inf.append((F, indiv))
                    elif d < INF and all(x < INF for x in indiv) and d > max(indiv):
                        positive.append((d - max(indiv), F, d, indiv))
            print("POSITIVE_INTERACTION_GAP", len(positive), "INFINITE_WITH_ALL_SINGLETONS_FINITE", len(hidden_inf))
            if positive:
                gap, F, d, indiv = max(positive, key=lambda x: (x[0], x[1]))
                print("MAX_INTERACTION_GAP", gap, "BUNDLE", ",".join(F), "JOINT", fmt(d), "SINGLETONS", ",".join(map(fmt, indiv)))
            if hidden_inf:
                F, indiv = hidden_inf[0]
                print("HIDDEN_IRREVERSIBILITY_WITNESS", ",".join(F), "SINGLETONS", ",".join(map(fmt, indiv)))
        all_results[sname] = results

    print("NESTED_TRANSFORMATION_CHAIN")
    chain = ["BASELINE"] + [f"SHARED_{k}_REPAIRABLE" for k in DELETE_LEVELS]
    for a, b in zip(chain, chain[1:]):
        delayed = irreversible = unchanged = easier = newly_available = 0
        for F, da in all_results[a].items():
            db = all_results[b][F]
            if da < INF and db >= INF:
                irreversible += 1
            elif da >= INF and db < INF:
                newly_available += 1
            elif da < INF and db < INF and db > da:
                delayed += 1
            elif da < INF and db < INF and db < da:
                easier += 1
            elif da == db:
                unchanged += 1
        print("TRANSFORM", a, "TO", b, "DELAYED", delayed, "NEW_IRREVERSIBLE", irreversible, "UNCHANGED", unchanged, "EASIER", easier, "NEWLY_AVAILABLE", newly_available)


if __name__ == "__main__":
    main()
