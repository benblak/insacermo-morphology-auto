import hashlib
import itertools
from collections import Counter

import cobra
from cobra.flux_analysis import pfba
from cobra.io import load_model
from cobra.util.solver import linear_reaction_coefficients

# Fixed-before-result cross-domain protocol.
# Model: BiGG iML1515 (E. coli K-12 MG1655 genome-scale reconstruction).
# Contract: maintain >=10% of wild-type biomass growth and simultaneously
# secrete each requested product at >=8% of its own baseline maximum under
# that growth floor. Destruction: reaction knockouts selected by a fixed
# shared-support rule among individually silent perturbations. Recovery depth
# is the exact minimum number of deleted reactions that must be restored.
# This is a constraint-based steady-state model, not a kinetic, regulatory,
# causal, clinical, or in-vivo viability claim.

MODEL_ID = "iML1515"
TARGET_EXCHANGES = (
    "EX_ac_e",      # acetate
    "EX_succ_e",    # succinate
    "EX_etoh_e",    # ethanol
    "EX_for_e",     # formate
    "EX_lac__D_e",  # D-lactate
    "EX_pyr_e",     # pyruvate
)
MAX_BUNDLE = 3
GROWTH_FRACTION = 0.10
TARGET_FRACTION = 0.08
SUPPORT_FLUX_EPS = 1e-7
CANDIDATE_SCAN = 80
DELETE_LEVELS = (4, 8, 12)
HASH_CONTROL = 8
PERMANENT_COUNT = 4
REPAIRABLE_AFTER_PERMANENT = 4
INF = 10**9


def biomass_reaction(model):
    coeffs = linear_reaction_coefficients(model)
    positive = [(float(v), r) for r, v in coeffs.items() if float(v) > 0]
    if not positive:
        raise RuntimeError("No positive linear biomass objective found")
    positive.sort(key=lambda x: (-x[0], x[1].id))
    return positive[0][1]


def feasible(model):
    sol = model.optimize()
    return sol.status == "optimal"


def baseline_requirements(model, biomass):
    wt = float(model.slim_optimize(error_value=float("nan")))
    if not (wt > 0):
        raise RuntimeError(f"Invalid WT growth {wt}")
    growth_floor = GROWTH_FRACTION * wt
    req = {}
    maxima = {}
    for rid in TARGET_EXCHANGES:
        if rid not in model.reactions:
            raise RuntimeError(f"Missing fixed target exchange {rid}")
        with model:
            biomass.lower_bound = max(biomass.lower_bound, growth_floor)
            target = model.reactions.get_by_id(rid)
            model.objective = target
            model.objective_direction = "max"
            vmax = float(model.slim_optimize(error_value=float("nan")))
        if not (vmax > 1e-8):
            raise RuntimeError(f"Target {rid} has non-positive baseline maximum {vmax}")
        maxima[rid] = vmax
        req[rid] = TARGET_FRACTION * vmax
    return wt, growth_floor, maxima, req


def impose_contract(model, biomass_id, growth_floor, bundle, req):
    biomass = model.reactions.get_by_id(biomass_id)
    biomass.lower_bound = max(biomass.lower_bound, growth_floor)
    for rid in bundle:
        r = model.reactions.get_by_id(rid)
        if r.upper_bound + 1e-9 < req[rid]:
            return False
        r.lower_bound = max(r.lower_bound, req[rid])
    return True


def singleton_feasible_after_knockout(model, biomass_id, growth_floor, req, rid):
    with model:
        model.reactions.get_by_id(rid).knock_out()
        for target in TARGET_EXCHANGES:
            with model:
                if not impose_contract(model, biomass_id, growth_floor, (target,), req):
                    return False
                if not feasible(model):
                    return False
    return True


def support_rank(model, biomass_id, growth_floor, req):
    # Shared-support score from six predeclared product contracts. For each
    # target, compute a parsimonious steady-state solution under the fixed
    # growth and secretion requirement. Rank non-boundary reactions by in how
    # many target solutions they carry nonzero flux, then by summed normalized
    # absolute flux. Candidate eligibility additionally requires every singleton
    # contract to survive that reaction's knockout.
    scores = Counter()
    magnitudes = Counter()
    for target in TARGET_EXCHANGES:
        with model:
            if not impose_contract(model, biomass_id, growth_floor, (target,), req):
                raise RuntimeError(f"Cannot impose singleton {target}")
            biomass = model.reactions.get_by_id(biomass_id)
            model.objective = biomass
            model.objective_direction = "max"
            sol = pfba(model, fraction_of_optimum=1.0)
            scale = max(1.0, float(sol.fluxes.abs().max()))
            for r in model.reactions:
                if r.boundary or r.id == biomass_id or r.id in TARGET_EXCHANGES:
                    continue
                v = abs(float(sol.fluxes[r.id]))
                if v > SUPPORT_FLUX_EPS:
                    scores[r.id] += 1
                    magnitudes[r.id] += v / scale

    ranked = sorted(scores, key=lambda rid: (-scores[rid], -magnitudes[rid], rid))
    eligible = []
    for rid in ranked[:CANDIDATE_SCAN]:
        r = model.reactions.get_by_id(rid)
        if r.lower_bound == 0 and r.upper_bound == 0:
            continue
        if singleton_feasible_after_knockout(model, biomass_id, growth_floor, req, rid):
            eligible.append(rid)
        if len(eligible) >= max(DELETE_LEVELS) + 8:
            break
    if len(eligible) < max(DELETE_LEVELS):
        raise RuntimeError(f"Only {len(eligible)} individually-silent candidates")
    return eligible, scores, magnitudes


def hash_rank(ids):
    return [rid for _, rid in sorted(
        (hashlib.sha256(("INSACERMO-IML1515-20260917|" + rid).encode()).hexdigest(), rid)
        for rid in ids
    )]


def scenarios(eligible):
    hashed = hash_rank(eligible)
    out = {"BASELINE": (set(), set())}
    for k in DELETE_LEVELS:
        out[f"SHARED_{k}_REPAIRABLE"] = (set(eligible[:k]), set())
    out[f"HASHED_{HASH_CONTROL}_REPAIRABLE"] = (set(hashed[:HASH_CONTROL]), set())
    out[f"SHARED_{PERMANENT_COUNT}_PERMANENT_PLUS_{REPAIRABLE_AFTER_PERMANENT}_REPAIRABLE"] = (
        set(eligible[PERMANENT_COUNT:PERMANENT_COUNT + REPAIRABLE_AFTER_PERMANENT]),
        set(eligible[:PERMANENT_COUNT]),
    )
    return out


def repair_depth(base_model, biomass_id, growth_floor, req, bundle, repairable, permanent):
    model = base_model.copy()
    if not impose_contract(model, biomass_id, growth_floor, bundle, req):
        return INF

    for rid in permanent:
        model.reactions.get_by_id(rid).knock_out()

    if not repairable:
        return 0 if feasible(model) else INF

    interface = model.solver.interface
    binaries = []
    for rid in sorted(repairable):
        r = model.reactions.get_by_id(rid)
        lb0, ub0 = float(r.lower_bound), float(r.upper_bound)
        y = interface.Variable(f"repair__{rid}", type="binary", lb=0, ub=1)
        model.add_cons_vars(y)
        binaries.append(y)
        # y=0 forces v=0; y=1 restores original bounds.
        model.add_cons_vars(interface.Constraint(r.flux_expression - ub0 * y, ub=0, name=f"rup__{rid}"))
        model.add_cons_vars(interface.Constraint(r.flux_expression - lb0 * y, lb=0, name=f"rlo__{rid}"))

    model.objective = interface.Objective(sum(binaries), direction="min")
    sol = model.optimize()
    if sol.status != "optimal":
        return INF
    return int(round(float(sol.objective_value)))


def fmt(d):
    return "INF" if d >= INF else str(int(d))


def main():
    model = load_model(MODEL_ID)
    biomass = biomass_reaction(model)
    biomass_id = biomass.id
    wt, growth_floor, maxima, req = baseline_requirements(model, biomass)
    eligible, support_count, support_mag = support_rank(model, biomass_id, growth_floor, req)
    scen = scenarios(eligible)

    print("INSACERMO_BLIND_IML1515_JOINT_METABOLIC_V1")
    print("MODEL", MODEL_ID, "REACTIONS", len(model.reactions), "METABOLITES", len(model.metabolites), "GENES", len(model.genes))
    print("BIOMASS", biomass_id, "WT_GROWTH", f"{wt:.9g}", "GROWTH_FLOOR", f"{growth_floor:.9g}")
    print("CONTRACT product secretion >= 8% own baseline max while growth >= 10% WT")
    print("TARGETS", " ".join(TARGET_EXCHANGES))
    print("TARGET_MAX", " ".join(f"{r}:{maxima[r]:.9g}" for r in TARGET_EXCHANGES))
    print("TARGET_REQ", " ".join(f"{r}:{req[r]:.9g}" for r in TARGET_EXCHANGES))
    print("DESTRUCTION_RULE shared pFBA support among individually-silent reaction knockouts")
    print("ELIGIBLE_RANK", " ".join(f"{r}:{support_count[r]}:{support_mag[r]:.6g}" for r in eligible[:20]))
    print("MAX_BUNDLE", MAX_BUNDLE)
    print("CAVEAT steady-state constraint-based reconstruction; no kinetic, regulatory, causal, clinical, or in-vivo viability claim")

    all_results = {}
    singleton_by_scenario = {}

    for sname, (repairable, permanent) in scen.items():
        print("SCENARIO", sname, "REPAIRABLE", len(repairable), "PERMANENT", len(permanent))
        singletons = {}
        for q in TARGET_EXCHANGES:
            singletons[q] = repair_depth(model, biomass_id, growth_floor, req, (q,), repairable, permanent)
        singleton_by_scenario[sname] = singletons
        print("SINGLETONS", " ".join(f"{q}:{fmt(singletons[q])}" for q in TARGET_EXCHANGES))

        results = {}
        for size in range(1, MAX_BUNDLE + 1):
            vals = []
            for F in itertools.combinations(TARGET_EXCHANGES, size):
                d = repair_depth(model, biomass_id, growth_floor, req, F, repairable, permanent)
                results[F] = d
                vals.append((F, d))

            finite = [(F, d) for F, d in vals if d < INF]
            infinite = [(F, d) for F, d in vals if d >= INF]
            hist = Counter(int(d) for _, d in finite)
            print("BUNDLE_SIZE", size, "TOTAL", len(vals), "FINITE", len(finite), "INFINITE", len(infinite))
            htxt = " ".join(f"D{k}:{hist[k]}" for k in sorted(hist))
            if infinite:
                htxt += (" " if htxt else "") + f"INF:{len(infinite)}"
            print("DEPTH_HIST", htxt)

            positive = []
            hidden_inf = []
            for F, d in vals:
                indiv = tuple(singletons[q] for q in F)
                if d >= INF:
                    if all(x < INF for x in indiv):
                        hidden_inf.append((F, indiv))
                    continue
                if all(x < INF for x in indiv):
                    gap = int(d - max(indiv))
                    if gap < 0:
                        raise AssertionError((sname, F, d, indiv))
                    if gap > 0:
                        positive.append((gap, F, d, indiv))

            print("POSITIVE_INTERACTION_GAP", len(positive))
            print("INFINITE_WITH_ALL_SINGLETONS_FINITE", len(hidden_inf))
            if positive:
                positive.sort(key=lambda x: (-x[0], x[1]))
                gap, F, d, indiv = positive[0]
                print("MAX_INTERACTION_GAP", gap, "BUNDLE", ",".join(F), "JOINT", fmt(d), "SINGLETONS", ",".join(map(fmt, indiv)))
            else:
                print("MAX_INTERACTION_GAP NA BUNDLE NA")
            if finite:
                F, d = max(finite, key=lambda x: (x[1], x[0]))
                print("MAX_FINITE_DEPTH", d, "BUNDLE", ",".join(F))
            else:
                print("MAX_FINITE_DEPTH NA BUNDLE NA")

            print("FIRST_JOINT_WITNESSES")
            shown = 0
            for gap, F, d, indiv in sorted(positive, key=lambda x: (-x[0], x[1])):
                print("WITNESS BUNDLE", ",".join(F), "JOINT", fmt(d), "SINGLETONS", ",".join(map(fmt, indiv)), "GAP", gap)
                shown += 1
                if shown >= 5:
                    break
            if shown < 5:
                for F, indiv in hidden_inf[:5-shown]:
                    print("WITNESS BUNDLE", ",".join(F), "JOINT INF SINGLETONS", ",".join(map(fmt, indiv)), "GAP INF")

        all_results[sname] = results

    chain = ["BASELINE"] + [f"SHARED_{k}_REPAIRABLE" for k in DELETE_LEVELS]
    print("NESTED_DAMAGE_CHAIN")
    for a, b in zip(chain, chain[1:]):
        ra, rb = all_results[a], all_results[b]
        delayed = irreversible = unchanged = 0
        finite_added = 0
        for F in ra:
            da, db = ra[F], rb[F]
            if da >= INF and db >= INF:
                unchanged += 1
            elif da < INF and db >= INF:
                irreversible += 1
            elif da < INF and db < INF and db > da:
                delayed += 1
                finite_added += int(db - da)
            elif db == da:
                unchanged += 1
            else:
                raise AssertionError(("destruction made recovery easier", a, b, F, da, db))
        print("TRANSFORM", a, "TO", b, "DELAYED", delayed, "NEW_IRREVERSIBLE", irreversible, "UNCHANGED", unchanged, "TOTAL_ADDED_FINITE_DEPTH", finite_added)


if __name__ == "__main__":
    main()
