# INSACERMO France V6 — rail investment under fiscal trajectories
# Exploratory sovereign-capability analysis. Not a forecast or policy recommendation.
#
# Current official anchors:
# - 2026 public deficit target: 5.0% GDP
# - objective: deficit below 3% GDP by 2029
#
# Only those anchors are official. Intermediate/post-2029 points below are
# transparent analytical scenarios.

from dataclasses import dataclass

DEBT_2025 = 3460.5
DEBT_RATIO_2025 = 1.157
INTEREST_2025 = 64.7
AFT_AVG_MATURITY_YEARS = 8.0 + 184.0 / 365.0
AFT_ISSUANCE_RATE_2025 = 0.0314

GDP_2025 = DEBT_2025 / DEBT_RATIO_2025
EFFECTIVE_RATE_2025 = INTEREST_2025 / DEBT_2025
ROLLOVER_SHARE = 1.0 / AFT_AVG_MATURITY_YEARS

START_YEAR = 2026
END_YEAR = 2033
PROGRAM_START = 2028
PROGRAM_YEARS = END_YEAR - PROGRAM_START + 1

CENTRAL_DEBT_CAP = 1.30
CENTRAL_INTEREST_CAP = 0.035

# Reference fiscal-path targets are total public deficit ratios.
# Consolidation is anchored at 5.0% in 2026 and <3% in 2029.
FISCAL_PATHS = {
    "consolidation": (0.050, 0.043, 0.036, 0.029, 0.027, 0.025, 0.023, 0.021),
    "stabilisation": (0.050, 0.050, 0.050, 0.050, 0.050, 0.050, 0.050, 0.050),
    "deterioration": (0.052, 0.054, 0.056, 0.058, 0.060, 0.062, 0.064, 0.066),
}

@dataclass(frozen=True)
class Macro:
    name: str
    nominal_gdp_growth: float
    market_refi_rate: float

MACROS = (
    Macro("reference_macro", 0.030, AFT_ISSUANCE_RATE_2025),
    Macro("combined_stress", 0.010, 0.050),
    Macro("severe_stress", 0.000, 0.060),
)

def calibrate_primary_path(total_deficit_targets):
    # Derive the primary-deficit path that hits each total-deficit target
    # under the reference macro environment, with zero extra rail borrowing.
    debt = DEBT_2025
    gdp = GDP_2025
    effective_rate = EFFECTIVE_RATE_2025
    primary_ratios = []
    ref = MACROS[0]
    for target in total_deficit_targets:
        gdp *= 1.0 + ref.nominal_gdp_growth
        effective_rate = (
            effective_rate * (1.0 - ROLLOVER_SHARE)
            + ref.market_refi_rate * ROLLOVER_SHARE
        )
        interest = debt * effective_rate
        primary_deficit_ratio = target - interest / gdp
        primary_ratios.append(primary_deficit_ratio)
        debt += target * gdp
    return tuple(primary_ratios)

PRIMARY_PATHS = {
    name: calibrate_primary_path(targets)
    for name, targets in FISCAL_PATHS.items()
}

def simulate(primary_path, macro, annual_extra_bn):
    debt = DEBT_2025
    gdp = GDP_2025
    effective_rate = EFFECTIVE_RATE_2025
    rows = []
    years = list(range(START_YEAR, END_YEAR + 1))
    for idx, year in enumerate(years):
        extra = annual_extra_bn if year >= PROGRAM_START else 0.0
        debt += extra
        gdp *= 1.0 + macro.nominal_gdp_growth
        effective_rate = (
            effective_rate * (1.0 - ROLLOVER_SHARE)
            + macro.market_refi_rate * ROLLOVER_SHARE
        )
        interest = debt * effective_rate
        primary_deficit = PRIMARY_PATHS[primary_path][idx] * gdp
        total_deficit = interest + primary_deficit
        debt += total_deficit
        rows.append({
            "year": year,
            "debt": debt,
            "gdp": gdp,
            "debt_ratio": debt / gdp,
            "interest_ratio": interest / gdp,
            "total_deficit_ratio": total_deficit / gdp,
        })
    return rows

def preserves_contract(rows):
    return all(
        r["debt_ratio"] <= CENTRAL_DEBT_CAP
        and r["interest_ratio"] <= CENTRAL_INTEREST_CAP
        for r in rows
    )

def max_annual_extra(primary_path, macro, step=0.1, max_bn=20.0):
    if not preserves_contract(simulate(primary_path, macro, 0.0)):
        return None
    best = 0.0
    n = int(round(max_bn / step))
    for i in range(n + 1):
        x = round(i * step, 10)
        if preserves_contract(simulate(primary_path, macro, x)):
            best = x
        else:
            break
    return best

ENVELOPES = (0.0, 1.5, 3.0, 5.0, 10.0)

print("INSACERMO_FRANCE_FISCAL_TRAJECTORY_RAIL_V6")
print("STATUS EXPLORATORY_FISCAL_PATH_CAPABILITY_FRONTIER")
print("OFFICIAL_ANCHOR_2026_DEFICIT_PCT", 5.0)
print("OFFICIAL_ANCHOR_2029_OBJECTIVE", "below_3_percent")
print("RULE intermediate_and_post_2029_paths_are_analytical_not_official_forecasts")
print("CENTRAL_CONTRACT_DEBT_CAP", 100 * CENTRAL_DEBT_CAP)
print("CENTRAL_CONTRACT_INTEREST_CAP", 100 * CENTRAL_INTEREST_CAP)

for path_name, targets in FISCAL_PATHS.items():
    print(
        "FISCAL_PATH",
        path_name,
        "TARGET_DEFICIT_RATIOS_PCT",
        ",".join(f"{100*x:.1f}" for x in targets),
    )
    print(
        "PRIMARY_PATH",
        path_name,
        "PRIMARY_DEFICIT_RATIOS_PCT",
        ",".join(f"{100*x:.4f}" for x in PRIMARY_PATHS[path_name]),
    )

    for macro in MACROS:
        base = simulate(path_name, macro, 0.0)
        end0 = base[-1]
        base_ok = preserves_contract(base)
        max_env = max_annual_extra(path_name, macro)
        print(
            "BASELINE",
            "FISCAL_PATH", path_name,
            "MACRO", macro.name,
            "CONTRACT_PRESERVED", int(base_ok),
            "YEAR2033_DEBT_RATIO", f"{100*end0['debt_ratio']:.6f}",
            "YEAR2033_INTEREST_RATIO", f"{100*end0['interest_ratio']:.6f}",
            "YEAR2033_DEFICIT_RATIO", f"{100*end0['total_deficit_ratio']:.6f}",
        )
        print(
            "MAX_ANNUAL_RAIL_EXTRA",
            "FISCAL_PATH", path_name,
            "MACRO", macro.name,
            "BN_PER_YEAR",
            "NONE_BASELINE_ALREADY_OUTSIDE" if max_env is None else f"{max_env:.1f}",
        )

        for annual in ENVELOPES:
            rows = simulate(path_name, macro, annual)
            end1 = rows[-1]
            delta_debt_ratio_pp = 100 * (end1["debt_ratio"] - end0["debt_ratio"])
            delta_interest_ratio_pp = 100 * (end1["interest_ratio"] - end0["interest_ratio"])
            print(
                "ENVELOPE",
                "FISCAL_PATH", path_name,
                "MACRO", macro.name,
                "ANNUAL_RAIL_EXTRA_BN", f"{annual:.1f}",
                "CUMULATIVE_2028_2033_BN", f"{annual*PROGRAM_YEARS:.1f}",
                "CONTRACT_PRESERVED", int(preserves_contract(rows)),
                "YEAR2033_DEBT_RATIO", f"{100*end1['debt_ratio']:.6f}",
                "YEAR2033_INTEREST_RATIO", f"{100*end1['interest_ratio']:.6f}",
                "DELTA_DEBT_RATIO_PP", f"{delta_debt_ratio_pp:.6f}",
                "DELTA_INTEREST_RATIO_PP", f"{delta_interest_ratio_pp:.6f}",
            )

print("LIMITATION fiscal paths are stylized except for the stated official anchors")
print("LIMITATION primary-balance paths are calibrated under the reference macro then held fixed under stress")
print("LIMITATION rail envelopes are fiscal capacity tests, not recommendations")
print("RESULT COMPLETE")
