# INSACERMO — Rhea high-order stoichiometric obstruction stress test V1
#
# Goal:
#   Find a REAL Rhea local module with a minimal lost future bundle of order > 2.
#
# Construction (generic, not hand-picked):
#   Choose k distinct explicit left-to-right Rhea reactions that each:
#     - consume exactly one unit of the same non-currency participant P,
#     - do not produce P,
#     - expose a distinct target product not initially present as a reactant.
#
#   Baseline inventory = sum of all k reactant multisets.
#   Destruction         = remove exactly one unit of P.
#
# Then every proper subbundle of the k target reactions is executable, because it
# consumes at most k-1 units of P, while the full k-bundle requires k units and
# cannot regenerate P.  Hence the full target bundle is a MINIMAL hard loss of
# order k in this local finite-inventory Petri-net semantics.
#
# We search automatically and prefer the largest clean witness up to MAX_K.
# This directly tests whether the order-2 SCC theorem is universal (it is not
# expected to be) while keeping the general INSACERMO bundle semantics intact.

from __future__ import annotations

import itertools
from collections import Counter, defaultdict

import rhea_stoichiometric_resource_stress_v1 as base

MAX_K = 6
MAX_RESOURCE_REACTION_FREQUENCY = 12


def novel_products(r):
    return set(r["right"]) - set(r["left"])


def choose_distinct_targets(rs):
    """Return one injective target assignment, all absent from every selected left side."""
    left_union = set()
    for r in rs:
        left_union |= set(r["left"])

    candidates = []
    for i, r in enumerate(rs):
        xs = sorted(x for x in novel_products(r) if x not in left_union)
        if not xs:
            return None
        candidates.append(xs)

    # Small k (<=6): deterministic backtracking for an injective assignment.
    assignment = [None] * len(rs)
    used = set()

    order = sorted(range(len(rs)), key=lambda i: (len(candidates[i]), i))

    def bt(j):
        if j == len(order):
            return True
        i = order[j]
        for x in candidates[i]:
            if x in used:
                continue
            # Target must be unique to this reaction among the selected right sides
            # to give a clean goal interpretation.
            if any(x in rs[h]["right"] for h in range(len(rs)) if h != i):
                continue
            used.add(x)
            assignment[i] = x
            if bt(j + 1):
                return True
            assignment[i] = None
            used.remove(x)
        return False

    return assignment if bt(0) else None


def execute_subset(inv, rs):
    """Execute the listed reactions in their deterministic listed order."""
    cur = inv.copy()
    for r in rs:
        cur = base.fire(cur, r["left"], r["right"])
        if cur is None:
            return None
    return cur


def fmt_counter(c, names):
    return "; ".join(
        f"{base.name_of(k, names)} [{k}] x{v}" for k, v in sorted(c.items())
    )


def main():
    raw = {k: base.download(v) for k, v in base.FILES.items()}
    lr_to_master, _ = base.parse_directions(raw["directions"])
    rxn_smiles, _ = base.parse_reaction_smiles(raw["reaction_smiles"])
    sm_to_ids, _ = base.parse_chebi_smiles(raw["chebi_smiles"])
    names = base.parse_names(raw["names"])

    reactions = []
    unresolved = 0
    for lr_id, master in lr_to_master.items():
        rxn = rxn_smiles.get(lr_id)
        if not rxn:
            continue
        left_sm, right_sm = rxn.split(">>", 1)
        left, ul = base.participant_counter(left_sm, sm_to_ids)
        right, ur = base.participant_counter(right_sm, sm_to_ids)
        if ul or ur or not left or not right:
            unresolved += 1
            continue
        if left == right:
            continue
        reactions.append({
            "lr": lr_id,
            "master": master,
            "left": left,
            "right": right,
            "rxn_smiles": rxn,
        })

    by_resource = defaultdict(list)
    for i, r in enumerate(reactions):
        for p, coeff in r["left"].items():
            if coeff == 1 and p not in r["right"] and not base.currency(p, names):
                by_resource[p].append(i)

    witnesses = []

    for p, idxs in by_resource.items():
        # Keep only one representative per Rhea master reaction.
        reps = []
        seen_master = set()
        for i in sorted(idxs, key=lambda z: int(reactions[z]["lr"])):
            m = reactions[i]["master"]
            if m in seen_master:
                continue
            seen_master.add(m)
            reps.append(i)

        freq = len(reps)
        if freq < 3 or freq > MAX_RESOURCE_REACTION_FREQUENCY:
            continue

        max_k_here = min(MAX_K, freq)
        found_for_resource = None

        # Prefer the highest-order clean witness.
        for k in range(max_k_here, 2, -1):
            for combo in itertools.combinations(reps, k):
                rs = [reactions[i] for i in combo]
                targets = choose_distinct_targets(rs)
                if targets is None:
                    continue

                baseline = Counter()
                for r in rs:
                    baseline += r["left"]

                # Exact resource semantics: each selected reaction consumes P once.
                if baseline[p] != k:
                    continue

                destroyed = baseline.copy()
                destroyed[p] -= 1

                # Full bundle must be feasible before destruction and infeasible after.
                before_full = execute_subset(baseline, rs) is not None
                after_full = execute_subset(destroyed, rs) is not None
                if not before_full or after_full:
                    continue

                # Minimality: every (k-1)-subbundle remains feasible after destruction.
                all_km1 = True
                for omit in range(k):
                    sub = [r for j, r in enumerate(rs) if j != omit]
                    if execute_subset(destroyed, sub) is None:
                        all_km1 = False
                        break
                if not all_km1:
                    continue

                # Repair with exactly one unit of P must restore the full bundle.
                repaired = destroyed.copy()
                repaired[p] += 1
                if execute_subset(repaired, rs) is None:
                    continue

                complexity = sum(sum(r["left"].values()) + sum(r["right"].values()) for r in rs)
                # For fixed k prefer rarer P and simpler reaction modules.
                score = (-k, freq, complexity, base.name_of(p, names), tuple(int(r["lr"]) for r in rs))
                found_for_resource = (score, p, rs, targets, baseline, destroyed)
                break
            if found_for_resource:
                break

        if found_for_resource:
            witnesses.append(found_for_resource)

    print("INSACERMO_RHEA_HIGH_ORDER_RESOURCE_OBSTRUCTION_V1")
    print("STATUS EXPLORATORY_REAL_CHEMISTRY_HIGH_ORDER_WITNESS")
    print("SEMANTICS FINITE_INVENTORY_PETRI_NET_LOCAL_MODULE")
    print("SCC_STATE_GOAL_ORDER2_THEOREM_APPLICABLE 0")
    print("GENERAL_INSACERMO_BUNDLE_SEMANTICS_APPLICABLE 1")
    print("SEARCH_MAX_K", MAX_K)
    print("PARSED_LR_REACTIONS", len(reactions))
    print("UNRESOLVED_LR_REACTIONS", unresolved)
    print("RESOURCES_WITH_CLEAN_HIGH_ORDER_WITNESS", len(witnesses))

    if not witnesses:
        print("RESULT NO_HIGH_ORDER_WITNESS_FOUND")
        return

    witnesses.sort(key=lambda x: x[0])
    score, p, rs, targets, baseline, destroyed = witnesses[0]
    k = len(rs)

    print("WITNESS_ORDER", k)
    print("SHARED_LIMITING_RESOURCE", base.name_of(p, names), p)
    print("RESOURCE_REACTION_FREQUENCY", len({r["master"] for r in reactions if p in r["left"] and r["left"][p] == 1 and p not in r["right"]}))
    print("BASELINE_RESOURCE_UNITS", baseline[p])
    print("AFTER_DESTRUCTION_RESOURCE_UNITS", destroyed[p])

    for idx, (r, t) in enumerate(zip(rs, targets), 1):
        print("BRANCH", idx, "LR", "RHEA:" + r["lr"], "MASTER", "RHEA:" + r["master"])
        print("BRANCH", idx, "LEFT", fmt_counter(r["left"], names))
        print("BRANCH", idx, "RIGHT", fmt_counter(r["right"], names))
        print("TARGET", idx, base.name_of(t, names), t)

    # Verify all lower-order proper bundles, not just k-1, using resource semantics.
    proper_total = 0
    proper_feasible = 0
    for size in range(1, k):
        for combo in itertools.combinations(range(k), size):
            proper_total += 1
            sub = [rs[i] for i in combo]
            if execute_subset(destroyed, sub) is not None:
                proper_feasible += 1

    print("FULL_BUNDLE_FEASIBLE_BEFORE", int(execute_subset(baseline, rs) is not None))
    print("FULL_BUNDLE_FEASIBLE_AFTER", int(execute_subset(destroyed, rs) is not None))
    print("PROPER_SUBBUNDLES_TOTAL", proper_total)
    print("PROPER_SUBBUNDLES_FEASIBLE_AFTER", proper_feasible)
    print("ALL_PROPER_SUBBUNDLES_FEASIBLE_AFTER", int(proper_total == proper_feasible))

    repaired = destroyed.copy()
    repaired[p] += 1
    print("FULL_BUNDLE_FEASIBLE_AFTER_ADD_ONE_RESOURCE_REPAIR", int(execute_subset(repaired, rs) is not None))
    print("MINIMAL_LOST_BUNDLE_ORDER", k)
    print("MECHANISM HIGH_ORDER_STOICHIOMETRIC_RESOURCE_COMPETITION")
    print("DESTRUCTION REMOVE_ONE_UNIT_OF_SHARED_RESOURCE")
    print("REPAIR ADD_ONE_UNIT_OF_SHARED_RESOURCE")
    print("INTERPRETATION order_2_is_not_universal_outside_state_goal_graph_class")
    print("LIMITATION local_module_not_global_metabolic_or_whole_cell_impossibility")
    print("RESULT COMPLETE")


if __name__ == "__main__":
    main()
