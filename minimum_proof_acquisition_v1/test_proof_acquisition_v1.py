from proof_acquisition_v1 import *

assert proof_deficit(100, 90) == 0
assert proof_deficit(100, 100) == 1
assert proof_deficit(100, 130) == 31

same = [
    AbsoluteBoundOffer("cheap_probe", 1, 95, "A"),
    AbsoluteBoundOffer("deep_probe", 10, 40, "B"),
    AbsoluteBoundOffer("useless", 0.1, 120, "C"),
]
p = plan_same_debt_absolute(reserve=100, baseline_upper_bound=130, offers=same)
assert p.restores_act and p.selected_sources == ("cheap_probe",)
assert p.total_cost == 1 and p.guaranteed_post_upper_bound == 95

p0 = plan_same_debt_absolute(reserve=100, baseline_upper_bound=90, offers=same)
assert p0.restores_act and p0.selected_sources == () and p0.total_cost == 0

pn = plan_same_debt_absolute(
    reserve=100, baseline_upper_bound=130,
    offers=[AbsoluteBoundOffer("no", 1, 100, "A")]
)
assert not pn.restores_act

components = {"sensor": 70, "regime": 60}
offers = [
    ComponentBoundOffer("sensor_fresh", "sensor", 1, 45, "S"),
    ComponentBoundOffer("sensor_deep", "sensor", 5, 30, "S2"),
    ComponentBoundOffer("regime_check", "regime", 2, 50, "R"),
]
pc = plan_additive_components(reserve=100, baseline_components=components, offers=offers)
assert pc.proof_deficit == 31
assert pc.selected_sources == ("regime_check", "sensor_fresh")
assert pc.total_cost == 3
assert pc.guaranteed_post_upper_bound == 95 and pc.restores_act

try:
    plan_additive_components(
        reserve=100,
        baseline_components=components,
        offers=[ComponentBoundOffer("bad", "sensor", 1, 80, "X")],
    )
except ProofAcquisitionError as e:
    assert str(e) == "OFFER_DOES_NOT_TIGHTEN"
else:
    raise AssertionError("worsening offer accepted")

print("MINIMUM_PROOF_ACQUISITION_V1_TESTS: PASS")
