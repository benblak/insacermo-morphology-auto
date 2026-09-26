# INSACERMO France V0.3 — Work-time transformation accounting
# Neutral accounting envelope, not a forecast or policy recommendation.
#
# Official baseline:
# DARES / INSEE, 2025:
# full-time salaried usual weekly hours = 38.9 h/week
# full-time salaried annual effective hours = 1656 h/year
#
# This experiment asks:
# If usual weekly hours are reduced, how much human time is released,
# and what compensating change is mechanically required to preserve
# annual income, total labour input, or output per worker?
#
# No causal claim is made about productivity, employment, health, or GDP.

BASE_WEEKLY_HOURS = 38.9
BASE_ANNUAL_EFFECTIVE_HOURS = 1656.0

TARGET_WEEKLY_HOURS = (37.0, 35.0, 32.0)

def pct(x):
    return 100.0 * x

print("INSACERMO_FRANCE_WORK_TIME_TRANSFORMATION_V0_3")
print("STATUS NEUTRAL_ACCOUNTING_ENVELOPE")
print("RULE NO_CAUSAL_PRODUCTIVITY_CLAIM")
print("RULE NO_POLICY_RANKING")
print("RULE NO_SINGLE_SOCIAL_SCORE")
print("BASE_WEEKLY_HOURS", BASE_WEEKLY_HOURS)
print("BASE_ANNUAL_EFFECTIVE_HOURS", BASE_ANNUAL_EFFECTIVE_HOURS)

for target in TARGET_WEEKLY_HOURS:
    ratio = target / BASE_WEEKLY_HOURS
    reduction = 1.0 - ratio

    # Stylized comparable annual-hours envelope:
    # annual effective hours scale with usual weekly hours.
    target_annual = BASE_ANNUAL_EFFECTIVE_HOURS * ratio
    annual_hours_freed = BASE_ANNUAL_EFFECTIVE_HOURS - target_annual
    weekly_hours_freed = BASE_WEEKLY_HOURS - target

    # If annual pay is fully preserved, implied hourly pay rises mechanically.
    hourly_pay_increase = (1.0 / ratio) - 1.0

    # If hourly pay is unchanged, annual pay falls with hours.
    proportional_annual_pay_change = -reduction

    # If output per worker must be unchanged with no hiring, this is the
    # required increase in output per hour.
    productivity_needed = (1.0 / ratio) - 1.0

    # If productivity is unchanged, this is the extra worker-equivalent
    # staffing needed to preserve the same aggregate labour-hours.
    staffing_needed = (1.0 / ratio) - 1.0

    print(
        "SCENARIO",
        "TARGET_WEEKLY_HOURS", f"{target:.1f}",
        "WEEKLY_HOURS_FREED", f"{weekly_hours_freed:.2f}",
        "HOURS_REDUCTION_PCT", f"{pct(reduction):.3f}",
        "STYLIZED_TARGET_ANNUAL_HOURS", f"{target_annual:.2f}",
        "ANNUAL_HOURS_FREED_PER_FULLTIME_SALARIED", f"{annual_hours_freed:.2f}",
        "FULL_PAY_PRESERVATION_HOURLY_PAY_INCREASE_PCT", f"{pct(hourly_pay_increase):.3f}",
        "UNCHANGED_HOURLY_PAY_ANNUAL_PAY_CHANGE_PCT", f"{pct(proportional_annual_pay_change):.3f}",
        "NO_HIRING_PRODUCTIVITY_REQUIRED_PCT", f"{pct(productivity_needed):.3f}",
        "NO_PRODUCTIVITY_EXTRA_STAFFING_EQUIVALENT_PCT", f"{pct(staffing_needed):.3f}",
    )

# A useful decomposition for later INSACERMO capability analysis:
print("CAPABILITY time_freedom directly_increases_when_hours_fall")
print("CAPABILITY material_freedom preserved_only_if_income_floor_is_preserved")
print("CAPABILITY employment may_change_but_requires_causal_model_not_accounting_identity")
print("CAPABILITY health may_change_but_requires_external_evidence_not_assumed_here")
print("CAPABILITY public_finance requires_tax_contribution_and_spending_model")
print("NEXT_LAYER add evidence-backed productivity and health response ranges")
print("NEXT_LAYER add low-income household floor and sector-specific staffing constraints")
print("RESULT COMPLETE")
