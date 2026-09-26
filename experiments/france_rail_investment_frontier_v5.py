# INSACERMO France V5 — rail investment envelope frontier
# Exploratory fiscal-capability frontier. Not a policy recommendation.
#
# V5 answers a narrow question:
# How much additional annual rail investment (2028-2033) can be layered on
# while tracking the marginal fiscal burden under the same sovereign model?
#
# It deliberately does NOT assume that physical rail capability scales
# linearly with money. The official +1.5bn/year programme remains the empirical
# benchmark; larger/smaller envelopes need separate engineering evidence.

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
PROGRAM_START = 2028

CENTRAL_DEBT_CAP = 1.30
CENTRAL_INTEREST_CAP = 0.035

ANNUAL_ENVELOPES_BN = (0.5, 1.0, 1.5, 2.0, 3.0, 4.0, 5.0)

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

def simulate(sc, annual_extra_bn):
    debt = DEBT_2025
    gdp = GDP_2025
    effective_rate = EFFECTIVE_RATE_2025
    rows = []
    for year in range(START_YEAR, END_YEAR + 1):
        extra = annual_extra_bn if year >= PROGRAM_START else 0.0
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
            "extra": extra,
            "debt": debt,
            "gdp": gdp,
            "debt_ratio": debt / gdp,
            "interest_ratio": interest / gdp,
        })
    return rows

def preserves_contract(rows):
    return all(
        r["debt_ratio"] <= CENTRAL_DEBT_CAP
        and r["interest_ratio"] <= CENTRAL_INTEREST_CAP
        for r in rows
    )

def max_annual_extra(sc, step=0.1, max_bn=20.0):
    # Only meaningful when the zero-extra baseline itself preserves contract.
    base = simulate(sc, 0.0)
    if not preserves_contract(base):
        return None
    best = 0.0
    n = int(round(max_bn / step))
    for i in range(n + 1):
        x = round(i * step, 10)
        if preserves_contract(simulate(sc, x)):
            best = x
        else:
            break
    return best

program_years = END_YEAR - PROGRAM_START + 1

print("INSACERMO_FRANCE_RAIL_INVESTMENT_FRONTIER_V5")
print("STATUS EXPLORATORY_ANNUAL_ENVELOPE_FRONTIER")
print("PROGRAM_YEARS", program_years)
print("CENTRAL_CONTRACT_DEBT_CAP", 100 * CENTRAL_DEBT_CAP)
print("CENTRAL_CONTRACT_INTEREST_CAP", 100 * CENTRAL_INTEREST_CAP)
print("RULE NO_LINEAR_CAPABILITY_SCALING_ASSUMED")
print("BENCHMARK_OFFICIAL_EXTRA_INVESTMENT_BN_PER_YEAR", 1.5)

for sc in SCENARIOS:
    base = simulate(sc, 0.0)
    base_ok = preserves_contract(base)
    end0 = base[-1]
    print(
        "BASELINE",
        "SCENARIO", sc.name,
        "CONTRACT_PRESERVED", int(base_ok),
        "YEAR2033_DEBT_RATIO", f"{100*end0['debt_ratio']:.6f}",
        "YEAR2033_INTEREST_RATIO", f"{100*end0['interest_ratio']:.6f}",
    )
    max_env = max_annual_extra(sc)
    print(
        "MAX_ANNUAL_EXTRA_WITHIN_CONTRACT",
        "SCENARIO", sc.name,
        "BN_PER_YEAR", "NONE_BASELINE_ALREADY_OUTSIDE" if max_env is None else f"{max_env:.1f}",
    )

    for annual in ANNUAL_ENVELOPES_BN:
        rows = simulate(sc, annual)
        end1 = rows[-1]
        cumulative = annual * program_years
        delta_debt_bn = end1["debt"] - end0["debt"]
        delta_debt_ratio_pp = 100.0 * (end1["debt_ratio"] - end0["debt_ratio"])
        delta_interest_ratio_pp = 100.0 * (end1["interest_ratio"] - end0["interest_ratio"])
        print(
            "ENVELOPE",
            "SCENARIO", sc.name,
            "ANNUAL_EXTRA_BN", f"{annual:.1f}",
            "CUMULATIVE_2028_2033_BN", f"{cumulative:.1f}",
            "CONTRACT_PRESERVED", int(preserves_contract(rows)),
            "DELTA_DEBT_BN", f"{delta_debt_bn:.6f}",
            "DELTA_DEBT_RATIO_PP", f"{delta_debt_ratio_pp:.6f}",
            "DELTA_INTEREST_RATIO_PP", f"{delta_interest_ratio_pp:.6f}",
            "YEAR2033_DEBT_RATIO", f"{100*end1['debt_ratio']:.6f}",
            "YEAR2033_INTEREST_RATIO", f"{100*end1['interest_ratio']:.6f}",
        )

print("LIMITATION envelopes are fiscal stress tests, not recommendations")
print("LIMITATION physical capability gains are not extrapolated beyond the official 1.5bn/year benchmark")
print("LIMITATION sectors compete for the same sovereign fiscal space; cross-sector optimization is a later layer")
print("RESULT COMPLETE")
