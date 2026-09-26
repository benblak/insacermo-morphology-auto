# INSACERMO France Sovereign Finance V3
# Marginal capability-return thresholds for debt-financed investment.
# Exploratory analysis only: not a forecast and not a policy recommendation.

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
        })
    return rows

def preserves(extra, sc, growth_uplift=0.0, annual_fiscal_dividend_bn=0.0):
    rows = simulate(extra, sc, growth_uplift, annual_fiscal_dividend_bn)
    return all(
        r["debt_ratio"] <= CENTRAL_DEBT_CAP
        and r["interest_ratio"] <= CENTRAL_INTEREST_CAP
        for r in rows
    )

def min_growth_uplift(extra, sc, max_bp=2000):
    for bp in range(max_bp + 1):
        uplift = bp / 10000.0
        if preserves(extra, sc, growth_uplift=uplift):
            return uplift
    return None

def min_fiscal_dividend(extra, sc, max_half_bn=1000):
    for half_bn in range(max_half_bn + 1):
        dividend = half_bn * 0.5
        if preserves(extra, sc, annual_fiscal_dividend_bn=dividend):
            return dividend
    return None

print("INSACERMO_FRANCE_SOVEREIGN_FINANCE_V3")
print("STATUS EXPLORATORY_MARGINAL_CAPABILITY_RETURN")
print("HORIZON_YEARS", HORIZON)
print("CENTRAL_CONTRACT_DEBT_CAP", 100 * CENTRAL_DEBT_CAP)
print("CENTRAL_CONTRACT_INTEREST_CAP", 100 * CENTRAL_INTEREST_CAP)
print("INTERPRETATION marginal threshold = extra requirement caused by new borrowing beyond baseline scenario requirement")
print("WARNING thresholds are model-implied analytical break-even requirements, not forecasts")

for sc in SCENARIOS:
    base_g = min_growth_uplift(0.0, sc)
    base_f = min_fiscal_dividend(0.0, sc)
    print(
        "BASELINE_REQUIREMENT",
        "SCENARIO", sc.name,
        "GROWTH_UPLIFT_PP", "NONE" if base_g is None else f"{100*base_g:.4f}",
        "ANNUAL_FISCAL_DIVIDEND_BN", "NONE" if base_f is None else f"{base_f:.1f}",
    )

    for extra in BORROWING_CASES:
        g = min_growth_uplift(extra, sc)
        f = min_fiscal_dividend(extra, sc)

        marginal_g = None
        if g is not None and base_g is not None:
            marginal_g = max(0.0, g - base_g)

        marginal_f = None
        if f is not None and base_f is not None:
            marginal_f = max(0.0, f - base_f)

        rows0 = simulate(0.0, sc)
        rowsx = simulate(extra, sc)
        year5_delta_debt_ratio = rowsx[-1]["debt_ratio"] - rows0[-1]["debt_ratio"]
        year5_delta_interest_ratio = rowsx[-1]["interest_ratio"] - rows0[-1]["interest_ratio"]

        print(
            "MARGINAL_THRESHOLD",
            "SCENARIO", sc.name,
            "BORROWING_BN", f"{extra:.1f}",
            "TOTAL_GROWTH_REQ_PP", "NONE" if g is None else f"{100*g:.4f}",
            "MARGINAL_GROWTH_REQ_PP", "NONE" if marginal_g is None else f"{100*marginal_g:.4f}",
            "TOTAL_FISCAL_REQ_BN", "NONE" if f is None else f"{f:.1f}",
            "MARGINAL_FISCAL_REQ_BN", "NONE" if marginal_f is None else f"{marginal_f:.1f}",
            "YEAR5_DELTA_DEBT_RATIO_PP", f"{100*year5_delta_debt_ratio:.6f}",
            "YEAR5_DELTA_INTEREST_RATIO_PP", f"{100*year5_delta_interest_ratio:.6f}",
        )

print("RESULT COMPLETE")
