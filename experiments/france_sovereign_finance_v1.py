# INSACERMO France Sovereign Finance V1
# Exploratory capability audit, not a forecast and not a fiscal recommendation.
#
# Official anchors:
# INSEE 2025 public accounts:
#   public debt end-2025 = EUR 3,460.5bn = 115.7% GDP
#   public deficit 2025 = EUR 152.5bn = 5.1% GDP
#   public interest expenditure 2025 = EUR 64.7bn
# AFT 2025:
#   negotiable State debt = EUR 2,737bn
#   average maturity = 8 years 184 days
#   average 2025 medium/long-term issuance rate = 3.14%
# AFT 2026 programme:
#   financing need = EUR 305.7bn
#   medium/long-term net issuance = EUR 310.0bn
#
# We deliberately do NOT mix this with the graph/SCC theorem.  This is a
# separate finite-horizon scenario audit for sovereign financial capacity.

from dataclasses import dataclass
from itertools import product

DEBT_2025 = 3460.5
DEBT_RATIO_2025 = 1.157
DEFICIT_2025 = 152.5
INTEREST_2025 = 64.7
AFT_NEGOTIABLE_DEBT_2025 = 2737.0
AFT_AVG_MATURITY_YEARS = 8.0 + 184.0 / 365.0
AFT_ISSUANCE_RATE_2025 = 0.0314
AFT_FINANCING_NEED_2026 = 305.7
AFT_NET_MLT_ISSUANCE_2026 = 310.0

GDP_2025 = DEBT_2025 / DEBT_RATIO_2025
PRIMARY_DEFICIT_2025 = DEFICIT_2025 - INTEREST_2025
PRIMARY_DEFICIT_RATIO = PRIMARY_DEFICIT_2025 / GDP_2025
EFFECTIVE_RATE_2025 = INTEREST_2025 / DEBT_2025
ROLLOVER_SHARE = 1.0 / AFT_AVG_MATURITY_YEARS

HORIZON = 5

@dataclass(frozen=True)
class Scenario:
    name: str
    nominal_gdp_growth: float
    market_refi_rate: float

# Stress assumptions, not forecasts.
SCENARIOS = (
    Scenario("reference_environment", 0.030, AFT_ISSUANCE_RATE_2025),
    Scenario("rate_stress", 0.030, 0.050),
    Scenario("growth_stress", 0.010, AFT_ISSUANCE_RATE_2025),
    Scenario("combined_stress", 0.010, 0.050),
    Scenario("severe_stress", 0.000, 0.060),
)

# Contract sensitivity grid. These are explicit analytical thresholds,
# not claims that any particular threshold is economically optimal.
DEBT_CAPS = (1.25, 1.30, 1.35)
INTEREST_CAPS = (0.030, 0.035, 0.040)

def simulate(extra_one_off_borrowing_bn: float, sc: Scenario):
    debt = DEBT_2025 + extra_one_off_borrowing_bn
    gdp = GDP_2025
    effective_rate = EFFECTIVE_RATE_2025
    rows = []
    for year in range(1, HORIZON + 1):
        gdp *= 1.0 + sc.nominal_gdp_growth
        effective_rate = (
            effective_rate * (1.0 - ROLLOVER_SHARE)
            + sc.market_refi_rate * ROLLOVER_SHARE
        )
        interest = debt * effective_rate
        primary_deficit = gdp * PRIMARY_DEFICIT_RATIO
        debt = debt + interest + primary_deficit
        rows.append({
            "year": year,
            "debt": debt,
            "gdp": gdp,
            "debt_ratio": debt / gdp,
            "effective_rate": effective_rate,
            "interest": interest,
            "interest_ratio": interest / gdp,
            "primary_deficit": primary_deficit,
        })
    return rows

def preserves(extra, sc, debt_cap, interest_cap):
    rows = simulate(extra, sc)
    return all(
        row["debt_ratio"] <= debt_cap
        and row["interest_ratio"] <= interest_cap
        for row in rows
    )

def max_extra(sc, debt_cap, interest_cap, max_search=500):
    best = None
    for extra in range(max_search + 1):
        if preserves(float(extra), sc, debt_cap, interest_cap):
            best = float(extra)
        else:
            # Monotone in this simple model.
            break
    return best

print("INSACERMO_FRANCE_SOVEREIGN_FINANCE_V1")
print("STATUS EXPLORATORY_CAPABILITY_AUDIT_NOT_FORECAST")
print("HORIZON_YEARS", HORIZON)
print("GDP_2025_IMPLIED_BN", f"{GDP_2025:.3f}")
print("PUBLIC_DEBT_2025_BN", DEBT_2025)
print("PUBLIC_DEBT_RATIO_2025", f"{100*DEBT_RATIO_2025:.3f}")
print("PUBLIC_DEFICIT_2025_BN", DEFICIT_2025)
print("PUBLIC_INTEREST_2025_BN", INTEREST_2025)
print("PRIMARY_DEFICIT_2025_BN", f"{PRIMARY_DEFICIT_2025:.3f}")
print("PRIMARY_DEFICIT_RATIO", f"{100*PRIMARY_DEFICIT_RATIO:.6f}")
print("IMPLIED_EFFECTIVE_INTEREST_RATE_2025", f"{100*EFFECTIVE_RATE_2025:.6f}")
print("AFT_NEGOTIABLE_DEBT_2025_BN", AFT_NEGOTIABLE_DEBT_2025)
print("AFT_AVG_MATURITY_YEARS", f"{AFT_AVG_MATURITY_YEARS:.6f}")
print("ROLLOVER_SHARE_PROXY", f"{ROLLOVER_SHARE:.9f}")
print("AFT_ISSUANCE_RATE_2025", f"{100*AFT_ISSUANCE_RATE_2025:.4f}")
print("AFT_FINANCING_NEED_2026_BN", AFT_FINANCING_NEED_2026)
print("AFT_NET_MLT_ISSUANCE_2026_BN", AFT_NET_MLT_ISSUANCE_2026)
print("AFT_FINANCING_NEED_AS_SHARE_IMPLIED_GDP", f"{100*AFT_FINANCING_NEED_2026/GDP_2025:.6f}")

for sc in SCENARIOS:
    zero = simulate(0.0, sc)[-1]
    print(
        "SCENARIO_ZERO_EXTRA", sc.name,
        "NOMINAL_GDP_GROWTH", f"{100*sc.nominal_gdp_growth:.3f}",
        "MARKET_REFI_RATE", f"{100*sc.market_refi_rate:.3f}",
        "YEAR5_DEBT_RATIO", f"{100*zero['debt_ratio']:.6f}",
        "YEAR5_INTEREST_RATIO", f"{100*zero['interest_ratio']:.6f}",
    )

for debt_cap, interest_cap in product(DEBT_CAPS, INTEREST_CAPS):
    vals = []
    for sc in SCENARIOS:
        headroom = max_extra(sc, debt_cap, interest_cap)
        vals.append((sc.name, headroom))
        print(
            "HEADROOM",
            "DEBT_CAP", f"{100*debt_cap:.1f}",
            "INTEREST_CAP", f"{100*interest_cap:.1f}",
            "SCENARIO", sc.name,
            "MAX_ONE_OFF_EXTRA_BORROWING_BN",
            "NONE" if headroom is None else f"{headroom:.1f}",
        )
    finite = [v for _, v in vals if v is not None]
    robust = min(finite) if len(finite) == len(vals) else None
    print(
        "ROBUST_HEADROOM",
        "DEBT_CAP", f"{100*debt_cap:.1f}",
        "INTEREST_CAP", f"{100*interest_cap:.1f}",
        "ALL_SCENARIOS_MAX_ONE_OFF_EXTRA_BORROWING_BN",
        "NONE" if robust is None else f"{robust:.1f}",
    )

# One illustrative central contract for a compact INSACERMO-style verdict.
CENTRAL_DEBT_CAP = 1.30
CENTRAL_INTEREST_CAP = 0.035
print("CENTRAL_CONTRACT_DEBT_CAP", 100*CENTRAL_DEBT_CAP)
print("CENTRAL_CONTRACT_INTEREST_CAP", 100*CENTRAL_INTEREST_CAP)
for sc in SCENARIOS:
    h = max_extra(sc, CENTRAL_DEBT_CAP, CENTRAL_INTEREST_CAP)
    print(
        "CENTRAL_CONTRACT_SCENARIO",
        sc.name,
        "MAX_ONE_OFF_EXTRA_BORROWING_BN",
        "NONE" if h is None else f"{h:.1f}",
    )

print("LIMITATION primary deficit ratio held constant at 2025 implied level")
print("LIMITATION maturity-based rate pass-through uses AFT State debt as a proxy for public-debt repricing")
print("LIMITATION thresholds are analytical contracts, not policy recommendations")
print("RESULT COMPLETE")
