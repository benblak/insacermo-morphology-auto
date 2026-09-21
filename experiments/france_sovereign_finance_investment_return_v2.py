# INSACERMO France Sovereign Finance V2
# Capability-return thresholds for debt-financed investment.
# Exploratory analysis: thresholds are not forecasts or policy recommendations.

from dataclasses import dataclass

DEBT_2025 = 3460.5
DEBT_RATIO_2025 = 1.157
DEFICIT_2025 = 152.5
INTEREST_2025 = 64.7
AFT_AVG_MATURITY_YEARS = 8.0 + 184.0 / 365.0
AFT_ISSUANCE_RATE_2025 = 0.0314

GDP_2025 = DEBT_2025 / DEBT_RATIO_2025
PRIMARY_DEFICIT_2025 = DEFICIT_2025 - INTEREST_2025
PRIMARY_DEFICIT_RATIO = PRIMARY_DEFICIT_2025 / GDP_2025
EFFECTIVE_RATE_2025 = INTEREST_2025 / DEBT_2025
ROLLOVER_SHARE = 1.0 / AFT_AVG_MATURITY_YEARS

HORIZON = 5
CENTRAL_DEBT_CAP = 1.30
CENTRAL_INTEREST_CAP = 0.035
BORROWING_CASES = (10.0, 50.0, 100.0)

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

def simulate(extra_borrowing_bn, sc, growth_uplift=0.0, annual_fiscal_dividend_bn=0.0):
    debt = DEBT_2025 + extra_borrowing_bn
    gdp = GDP_2025
    effective_rate = EFFECTIVE_RATE_2025
    rows = []
    for year in range(1, HORIZON + 1):
        gdp *= 1.0 + sc.nominal_gdp_growth + growth_uplift
        effective_rate = (
            effective_rate * (1.0 - ROLLOVER_SHARE)
            + sc.market_refi_rate * ROLLOVER_SHARE
        )
        interest = debt * effective_rate
        primary_deficit = gdp * PRIMARY_DEFICIT_RATIO - annual_fiscal_dividend_bn
        debt = debt + interest + primary_deficit
        rows.append({
            "year": year,
            "debt": debt,
            "gdp": gdp,
            "debt_ratio": debt / gdp,
            "interest": interest,
            "interest_ratio": interest / gdp,
            "primary_deficit": primary_deficit,
        })
    return rows

def preserves(extra, sc, growth_uplift=0.0, annual_fiscal_dividend_bn=0.0):
    rows = simulate(extra, sc, growth_uplift, annual_fiscal_dividend_bn)
    return all(
        r["debt_ratio"] <= CENTRAL_DEBT_CAP
        and r["interest_ratio"] <= CENTRAL_INTEREST_CAP
        for r in rows
    )

def min_growth_uplift(extra, sc):
    # Search 0 to +10 percentage points of sustained nominal GDP growth uplift.
    for bp in range(0, 1001):  # 1 bp increments
        uplift = bp / 10000.0
        if preserves(extra, sc, growth_uplift=uplift):
            return uplift
    return None

def min_fiscal_dividend(extra, sc):
    # Search 0 to EUR 250bn/year, in EUR 0.5bn increments.
    for half_bn in range(0, 501):
        dividend = half_bn * 0.5
        if preserves(extra, sc, annual_fiscal_dividend_bn=dividend):
            return dividend
    return None

print("INSACERMO_FRANCE_SOVEREIGN_FINANCE_V2")
print("STATUS EXPLORATORY_CAPABILITY_RETURN_THRESHOLDS")
print("HORIZON_YEARS", HORIZON)
print("CENTRAL_CONTRACT_DEBT_CAP", 100 * CENTRAL_DEBT_CAP)
print("CENTRAL_CONTRACT_INTEREST_CAP", 100 * CENTRAL_INTEREST_CAP)
print("INTERPRETATION growth threshold = sustained nominal GDP growth uplift required")
print("INTERPRETATION fiscal threshold = annual primary-balance improvement required")
print("WARNING thresholds are break-even analytical requirements, not expected sector returns")

for extra in BORROWING_CASES:
    print("BORROWING_CASE_BN", extra)
    growth_requirements = []
    fiscal_requirements = []
    for sc in SCENARIOS:
        g = min_growth_uplift(extra, sc)
        f = min_fiscal_dividend(extra, sc)
        growth_requirements.append(g)
        fiscal_requirements.append(f)
        print(
            "RETURN_THRESHOLD",
            "BORROWING_BN", f"{extra:.1f}",
            "SCENARIO", sc.name,
            "MIN_SUSTAINED_NOMINAL_GDP_GROWTH_UPLIFT_PP",
            "NONE" if g is None else f"{100*g:.4f}",
            "MIN_ANNUAL_FISCAL_DIVIDEND_BN",
            "NONE" if f is None else f"{f:.1f}",
        )

    robust_growth = None if any(v is None for v in growth_requirements) else max(growth_requirements)
    robust_fiscal = None if any(v is None for v in fiscal_requirements) else max(fiscal_requirements)
    print(
        "ROBUST_RETURN_THRESHOLD",
        "BORROWING_BN", f"{extra:.1f}",
        "ALL_SCENARIOS_GROWTH_UPLIFT_PP",
        "NONE" if robust_growth is None else f"{100*robust_growth:.4f}",
        "ALL_SCENARIOS_ANNUAL_FISCAL_DIVIDEND_BN",
        "NONE" if robust_fiscal is None else f"{robust_fiscal:.1f}",
    )

    # Also show the pure-cost counterfactual.
    ref = simulate(extra, SCENARIOS[0])[-1]
    severe = simulate(extra, SCENARIOS[-1])[-1]
    print(
        "NO_RETURN_YEAR5",
        "BORROWING_BN", f"{extra:.1f}",
        "REFERENCE_DEBT_RATIO", f"{100*ref['debt_ratio']:.6f}",
        "REFERENCE_INTEREST_RATIO", f"{100*ref['interest_ratio']:.6f}",
        "SEVERE_DEBT_RATIO", f"{100*severe['debt_ratio']:.6f}",
        "SEVERE_INTEREST_RATIO", f"{100*severe['interest_ratio']:.6f}",
    )

print("LIMITATION growth uplift is stylized and sustained uniformly for five years")
print("LIMITATION fiscal dividend is modeled as a fixed annual primary-balance improvement")
print("LIMITATION no sector is assigned a return; empirical sector mapping is a separate step")
print("RESULT COMPLETE")
