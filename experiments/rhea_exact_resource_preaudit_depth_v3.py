# INSACERMO — Rhea exact resource pre-audit depth V3
#
# Purpose
# -------
# Derive an audit-depth bound BEFORE enumerating proper future bundles, using a
# certificate class entirely different from the PGLib/Farkas case.
#
# Frozen real-data module:
# ten explicit left-to-right Rhea reactions from the previously audited
# naringenin witness.  Each consumes exactly one unit of (2S)-naringenin and
# none regenerates it.
#
# Destruction removes one unit of the shared resource:
#   baseline resource units = 10
#   post-destruction capacity C = 9
#   per-goal burden delta = 1
#
# Any inclusion-minimal resource obstruction of m selected goals must have every
# (m-1)-goal deletion fit in capacity C, hence
#   (m-1) * delta <= C
# and therefore
#   m <= 1 + floor(C/delta) = 10.
#
# This script derives r_pre=10 from stoichiometry/capacity only. It does NOT
# enumerate goal bundles and does NOT call the Petri execution audit.

from __future__ import annotations

import hashlib

import rhea_equation_level_petri_v2 as base

FROZEN_LR = (
    "15434",
    "31540",
    "32756",
    "35488",
    "57589",
    "61085",
    "61097",
    "61105",
    "65153",
    "73288",
)
RESOURCE = "(2S)-naringenin"
BASELINE_RESOURCE_UNITS = 10
DESTRUCTION_UNITS = 1


def main():
    rawd = base.dl(base.DIRECTIONS_URL)
    rawn = base.dl(base.NAMES_URL)
    rawrest = base.dl(base.REST_URL)

    dirs = base.parse_dirs(rawd)
    reactions, rejected = base.parse_rest(rawrest, dirs)
    by_lr = {r["lr"]: r for r in reactions}

    missing = [lr for lr in FROZEN_LR if lr not in by_lr]
    if missing:
        raise RuntimeError(f"frozen Rhea LR reactions missing: {missing}")

    burdens = []
    for lr in FROZEN_LR:
        r = by_lr[lr]
        left = r["left"].get(RESOURCE, 0)
        right = r["right"].get(RESOURCE, 0)

        if left != 1:
            raise RuntimeError(
                f"RHEA:{lr} no longer has unit {RESOURCE} burden: left={left}"
            )
        if right != 0:
            raise RuntimeError(
                f"RHEA:{lr} regenerates {RESOURCE}: right={right}"
            )

        burdens.append(left)

    delta = min(burdens)
    if delta <= 0:
        raise RuntimeError("nonpositive resource burden")

    capacity = BASELINE_RESOURCE_UNITS - DESTRUCTION_UNITS
    if capacity < 0:
        raise RuntimeError("negative post-destruction capacity")

    # Integer resource-capacity certificate:
    # (m-1)*delta <= C  =>  m <= 1 + floor(C/delta).
    r_pre = 1 + capacity // delta

    print("INSACERMO_RHEA_EXACT_RESOURCE_PREAUDIT_DEPTH_V3")
    print("STATUS EXACT_INTEGER_RESOURCE_PREAUDIT_BOUND")
    print("SEMANTICS FROZEN_REAL_RHEA_LOCAL_FINITE_INVENTORY_MODULE")
    print("SOURCE_DIRECTIONS_SHA256", hashlib.sha256(rawd).hexdigest())
    print("SOURCE_NAMES_SHA256", hashlib.sha256(rawn).hexdigest())
    print("SOURCE_REST_SHA256", hashlib.sha256(rawrest).hexdigest())
    print("PARSED_LR_EQUATIONS", len(reactions))
    print("REJECTED_OR_NONINTEGER_EQUATIONS", rejected)
    print("FROZEN_REACTIONS", len(FROZEN_LR))
    print("FROZEN_LR_IDS", ",".join(FROZEN_LR))
    print("SHARED_LIMITING_RESOURCE", RESOURCE)
    print("ALL_FROZEN_REACTIONS_UNIT_RESOURCE_BURDEN", int(all(x == 1 for x in burdens)))
    print("NO_FROZEN_REACTION_REGENERATES_RESOURCE", 1)
    print("BASELINE_RESOURCE_UNITS", BASELINE_RESOURCE_UNITS)
    print("DESTRUCTION_REMOVE_RESOURCE_UNITS", DESTRUCTION_UNITS)
    print("POST_DESTRUCTION_CAPACITY", capacity)
    print("MIN_GOAL_BURDEN_DELTA", delta)
    print("BUNDLE_FEASIBILITY_CALLS_TO_DERIVE_R", 0)
    print("BUNDLE_ENUMERATION_USED_TO_DERIVE_R", 0)
    print("EXECUTION_SIMULATION_USED_TO_DERIVE_R", 0)
    print("RESOURCE_CERTIFICATE_FORMULA", "m<=1+floor(C/delta)")
    print("EXACT_RESOURCE_PREAUDIT_R", r_pre)
    print("LIMITATION frozen_local_Rhea_module_not_global_replenishment_or_whole_cell")
    print("RESULT COMPLETE")


if __name__ == "__main__":
    main()
