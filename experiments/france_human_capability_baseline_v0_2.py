# INSACERMO France V0.2 — Human Capability Baseline
# Public-data snapshot. No scalar social score, no party/policy preference.
#
# Sources (official public statistics):
# INSEE — Niveau de vie et pauvreté en 2024, published 2026-07-09
#   https://www.insee.fr/fr/statistiques/9019316
# INSEE — Consommation des ménages en 2025, published 2026
#   https://www.insee.fr/fr/statistiques/9006503
# DARES — La durée individuelle du travail, updated 2026-06-05
#   https://dares.travail-emploi.gouv.fr/donnees/la-duree-individuelle-du-travail
# DREES — Accessibilité aux soins de premier recours en 2024, published 2026-07-22
#   https://drees.solidarites-sante.gouv.fr/communique-de-presse-jeux-de-donnees/jeux-de-donnees/260722-accessibilite-aux-soins-de-premier-recours-en-2024

from dataclasses import dataclass
from typing import Optional

@dataclass(frozen=True)
class Indicator:
    capability: str
    name: str
    value: float
    unit: str
    year: int
    population: str
    direction: Optional[str] = None
    note: str = ""

INDICATORS = [
    # Material freedom / ability to live
    Indicator("material_freedom", "median_living_standard_monthly", 2228.0, "EUR/month/consumption-unit", 2024,
              "France metropolitan, ordinary households"),
    Indicator("material_freedom", "poverty_threshold_monthly", 1337.0, "EUR/month/consumption-unit", 2024,
              "France metropolitan, ordinary households"),
    Indicator("material_freedom", "poverty_rate", 15.4, "percent", 2024,
              "France metropolitan, ordinary households"),
    Indicator("material_freedom", "poverty_rate_people_in_employment", 8.5, "percent", 2024,
              "People in employment, age 18+"),
    Indicator("material_freedom", "poverty_rate_salaried", 6.9, "percent", 2024,
              "Salaried people, age 18+"),
    Indicator("material_freedom", "arbitrable_purchasing_power_per_CU_yoy", -1.4, "percent_yoy", 2025,
              "Households, national accounts", "down",
              "Income after pre-committed expenditure, per consumption unit."),

    # Time
    Indicator("time_freedom", "annual_effective_work_all_employed", 1585.0, "hours/year", 2025,
              "All employed people"),
    Indicator("time_freedom", "usual_weekly_work_all_employed", 36.8, "hours/week", 2025,
              "All employed people"),
    Indicator("time_freedom", "annual_effective_work_fulltime_salaried", 1656.0, "hours/year", 2025,
              "Full-time salaried"),
    Indicator("time_freedom", "usual_weekly_work_fulltime_salaried", 38.9, "hours/week", 2025,
              "Full-time salaried"),
    Indicator("time_freedom", "annual_effective_work_fulltime_selfemployed", 2152.0, "hours/year", 2025,
              "Full-time self-employed"),
    Indicator("time_freedom", "usual_weekly_work_fulltime_selfemployed", 46.6, "hours/week", 2025,
              "Full-time self-employed"),

    # Health access
    Indicator("health_access", "gp_APL_mean", 3.3, "consultations/year/standardized-inhabitant", 2024,
              "France excluding Mayotte", "down",
              "DREES APL; -1.1% versus 2023."),
    Indicator("health_access", "gp_APL_bottom10", 1.3, "consultations/year/standardized-inhabitant", 2024,
              "10% least well-served population"),
    Indicator("health_access", "gp_APL_top10", 5.7, "consultations/year/standardized-inhabitant", 2024,
              "10% best-served population"),
    Indicator("health_access", "gp_APL_top_bottom_ratio", 4.3, "ratio", 2024,
              "Top 10% / bottom 10%", "widening",
              "Ratio increased 5.3% versus 2023."),
]

CAPABILITY_CONTRACT = (
    "material_freedom",
    "time_freedom",
    "health_access",
)

def get(name: str) -> Indicator:
    return next(x for x in INDICATORS if x.name == name)

median = get("median_living_standard_monthly").value
poverty_threshold = get("poverty_threshold_monthly").value
material_margin = median - poverty_threshold

gp_mean = get("gp_APL_mean").value
gp_bottom = get("gp_APL_bottom10").value
gp_top = get("gp_APL_top10").value
gp_bottom_gap_from_mean = 1.0 - gp_bottom / gp_mean
gp_top_gap_from_bottom = gp_top - gp_bottom

ft_salary_hours = get("annual_effective_work_fulltime_salaried").value
ft_self_hours = get("annual_effective_work_fulltime_selfemployed").value
self_vs_salary_hours = ft_self_hours - ft_salary_hours

print("INSACERMO_FRANCE_HUMAN_CAPABILITY_BASELINE_V0_2")
print("STATUS PUBLIC_DATA_BASELINE_NO_POLICY_RANKING")
print("RULE NO_SCALAR_SOCIAL_SCORE")
print("RULE HUMAN_THRESHOLDS_NOT_IMPOSED_BY_ENGINE")
print("CONTRACT", ",".join(CAPABILITY_CONTRACT))

for x in INDICATORS:
    print(
        "INDICATOR",
        "CAPABILITY", x.capability,
        "NAME", x.name,
        "VALUE", x.value,
        "UNIT", x.unit,
        "YEAR", x.year,
        "DIRECTION", x.direction or "not_assigned",
    )

print("DERIVED material_median_minus_poverty_threshold_eur_month", f"{material_margin:.2f}")
print("DERIVED gp_bottom10_shortfall_vs_mean_pct", f"{100*gp_bottom_gap_from_mean:.3f}")
print("DERIVED gp_top10_minus_bottom10_consultations", f"{gp_top_gap_from_bottom:.3f}")
print("DERIVED fulltime_selfemployed_minus_salaried_hours_year", f"{self_vs_salary_hours:.1f}")

# Descriptive alerts only; these are not normative policy verdicts.
alerts = []
if get("arbitrable_purchasing_power_per_CU_yoy").value < 0:
    alerts.append("MATERIAL_FREEDOM_ARBITRABLE_PURCHASING_POWER_DOWN")
if get("gp_APL_mean").direction == "down":
    alerts.append("HEALTH_PRIMARY_CARE_ACCESS_DOWN")
if get("gp_APL_top_bottom_ratio").direction == "widening":
    alerts.append("HEALTH_TERRITORIAL_GAP_WIDENING")

for a in alerts:
    print("DESCRIPTIVE_ALERT", a)

print("NEXT_LAYER scenario transformations must report each capability separately")
print("NEXT_LAYER add territorial microdata and commuting/access network")
print("NEXT_LAYER add human-selected minimum floors before ACT/PROBE/REFUSE decisions")
print("RESULT COMPLETE")
