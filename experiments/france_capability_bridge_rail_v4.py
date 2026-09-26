# INSACERMO France V4 — sovereign finance <-> rail capability bridge
# Exploratory multi-dimensional capability accounting, not a cost-benefit forecast.
#
# Official 2026 transport contract anchors:
# - extra regeneration/modernisation investment from 2028: EUR 1.5bn/year
# - total regeneration/modernisation investment from 2028: EUR 4.5bn/year
# - target traffic growth by 2033 vs 2024: +25%
# - about 800,000 additional TGV/TER/freight trains in 2033 vs 2024
# - track renewal: 1,000 km/year vs 750 currently
# - catenary regeneration: +25%, reaching 330 km/year
# - civil engineering structures: 45/year vs about 30 currently
#
# We do NOT scalarize these into one "social ROI". Human decision-makers must
# choose any normative weights. This script only puts financial consumption
# and physical capability gains side-by-side.

from dataclasses import dataclass

DEBT_2025 = 3460.5
DEBT_RATIO_2025 = 1.157
DEFICIT_2025 = 152.5
INTEREST_2025 = 64.7
AFT_AVG_MATURITY_YEARS = 8.0 + 184.0 / 365.0
AFT_ISSUANCE_RATE_2025 = 0.0314

GDP_2025 = DEBT_2025 / DEBT_RATIO_2025
PRIMARY_DEFICIT_RATIO = (DEFICIT_2025 - INTEREST_2025) / GDP_2025
EFFECTIVE_RATE_2025 = INTEREST_2025 / DEBT_2025
ROLLOVER_SHARE = 1.0 / AFT_AVG_MATURITY_YEARS

START_YEAR = 2026
END_YEAR = 2033
EXTRA_INVESTMENT_START = 2028
EXTRA_INVESTMENT_BN_PER_YEAR = 1.5
TOTAL_REGEN_MODERN_BN_PER_YEAR = 4.5

TRAFFIC_TARGET_PCT = 25.0
EXTRA_TRAINS_2033 = 800000
TRACK_BASE_KM_PER_YEAR = 750
TRACK_TARGET_KM_PER_YEAR = 1000
CATENARY_TARGET_KM_PER_YEAR = 330
CATENARY_INCREASE_PCT = 25.0
STRUCTURES_BASE_PER_YEAR = 30
STRUCTURES_TARGET_PER_YEAR = 45

@dataclass(frozen=True)
class Scenario:
    name: str
    nominal_gdp_growth: float
    market_refi_rate: float

SCENARIOS = (
    Scenario("reference_environment", 0.030, AFT_ISSUANCE_RATE_2025),
    Scenario("rate_stress", 0.030, 0.050),
    Scenario("growth_stress", 0.010, AFT_ISSUANCE_RATE_2025),
    Scenario("combined_stress", 0.010, 0.050),
    Scenario("severe_stress", 0.000, 0.060),
)

def simulate(sc, with_program):
    debt = DEBT_2025
    gdp = GDP_2025
    effective_rate = EFFECTIVE_RATE_2025
    rows = []
    for year in range(START_YEAR, END_YEAR + 1):
        extra = (
            EXTRA_INVESTMENT_BN_PER_YEAR
            if with_program and year >= EXTRA_INVESTMENT_START
            else 0.0
        )
        debt += extra
        gdp *= 1.0 + sc.nominal_gdp_growth
        effective_rate = (
            effective_rate * (1.0 - ROLLOVER_SHARE)
            + sc.market_refi_rate * ROLLOVER_SHARE
        )
        interest = debt * effective_rate
        primary_deficit = gdp * PRIMARY_DEFICIT_RATIO
        debt += interest + primary_deficit
        rows.append({
            "year": year,
            "extra_investment": extra,
            "debt": debt,
            "gdp": gdp,
            "debt_ratio": debt / gdp,
            "interest_ratio": interest / gdp,
        })
    return rows

program_years = END_YEAR - EXTRA_INVESTMENT_START + 1
incremental_program_bn = program_years * EXTRA_INVESTMENT_BN_PER_YEAR

track_extra_km_per_year = TRACK_TARGET_KM_PER_YEAR - TRACK_BASE_KM_PER_YEAR
track_increase_pct = 100.0 * track_extra_km_per_year / TRACK_BASE_KM_PER_YEAR
catenary_base_implied = CATENARY_TARGET_KM_PER_YEAR / (1.0 + CATENARY_INCREASE_PCT / 100.0)
catenary_extra_km_per_year = CATENARY_TARGET_KM_PER_YEAR - catenary_base_implied
structures_extra_per_year = STRUCTURES_TARGET_PER_YEAR - STRUCTURES_BASE_PER_YEAR
structures_increase_pct = 100.0 * structures_extra_per_year / STRUCTURES_BASE_PER_YEAR

print("INSACERMO_FRANCE_CAPABILITY_BRIDGE_V4")
print("STATUS EXPLORATORY_MULTI_DIMENSIONAL_CAPABILITY_ACCOUNTING")
print("RULE NO_SCALAR_SOCIAL_ROI_WITHOUT_HUMAN_WEIGHTS")
print("PROGRAM_YEARS", program_years)
print("EXTRA_INVESTMENT_BN_PER_YEAR", EXTRA_INVESTMENT_BN_PER_YEAR)
print("INCREMENTAL_PROGRAM_2028_2033_BN", incremental_program_bn)
print("EXTRA_INVESTMENT_SHARE_2025_GDP_PCT", f"{100*EXTRA_INVESTMENT_BN_PER_YEAR/GDP_2025:.6f}")
print("CUMULATIVE_INCREMENT_SHARE_2025_GDP_PCT", f"{100*incremental_program_bn/GDP_2025:.6f}")

print("CAPABILITY traffic_target_pct", TRAFFIC_TARGET_PCT)
print("CAPABILITY extra_trains_2033_vs_2024", EXTRA_TRAINS_2033)
print("CAPABILITY track_target_km_per_year", TRACK_TARGET_KM_PER_YEAR)
print("CAPABILITY track_extra_km_per_year", track_extra_km_per_year)
print("CAPABILITY track_increase_pct", f"{track_increase_pct:.6f}")
print("CAPABILITY catenary_target_km_per_year", CATENARY_TARGET_KM_PER_YEAR)
print("CAPABILITY catenary_extra_km_per_year_implied", f"{catenary_extra_km_per_year:.6f}")
print("CAPABILITY structures_target_per_year", STRUCTURES_TARGET_PER_YEAR)
print("CAPABILITY structures_extra_per_year", structures_extra_per_year)
print("CAPABILITY structures_increase_pct", f"{structures_increase_pct:.6f}")

for sc in SCENARIOS:
    base = simulate(sc, False)
    prog = simulate(sc, True)
    end0 = base[-1]
    end1 = prog[-1]
    delta_debt_ratio_pp = 100.0 * (end1["debt_ratio"] - end0["debt_ratio"])
    delta_interest_ratio_pp = 100.0 * (end1["interest_ratio"] - end0["interest_ratio"])
    delta_debt_bn = end1["debt"] - end0["debt"]
    print(
        "FINANCIAL_FREEDOM_CONSUMED",
        "SCENARIO", sc.name,
        "YEAR", END_YEAR,
        "DELTA_DEBT_BN", f"{delta_debt_bn:.6f}",
        "DELTA_DEBT_RATIO_PP", f"{delta_debt_ratio_pp:.6f}",
        "DELTA_INTEREST_RATIO_PP", f"{delta_interest_ratio_pp:.6f}",
    )

print("INTERPRETATION capability figures are official programme targets/production levels, not guaranteed causal effects")
print("INTERPRETATION financial deltas are stylized model-implied marginal burdens under identical macro scenarios")
print("LIMITATION no monetization of health, time, territorial equity, climate, or resilience benefits")
print("RESULT COMPLETE")
