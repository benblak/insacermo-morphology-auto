from adaptive_proof_acquisition_v2 import *

worlds=[
    FiniteWorld("w1",90),
    FiniteWorld("w2",85),
    FiniteWorld("w3",80),
    FiniteWorld("w4",75),
]

# First probe: B closes ACT immediately, A remains too coarse.
p1=CertifiedAdaptiveProbe(
    "coarse_split",1,
    {"w1":"A","w2":"A","w3":"B","w4":"B"},
    {"A":110,"B":90},
    None,
    "authority-coarse",
)

# Fine probe has no globally sufficient certificate. It becomes certifiable only
# after context A = {w1,w2} has already been established by p1.
p2=CertifiedAdaptiveProbe(
    "fine_split",2,
    {"w1":"X","w2":"Y","w3":"X","w4":"Y"},
    {},
    {
      "w1,w2::X":90,
      "w1,w2::Y":85,
    },
    "authority-fine",
)

validate_probe_soundness(worlds,p1)
validate_probe_soundness(worlds,p2)

plan=plan_guaranteed_act(
    reserve=100,
    baseline_upper_bound=130,
    worlds=worlds,
    probes=[p1,p2],
)
assert plan.kind=="PROBE"
assert plan.probe_id=="coarse_split"
assert plan.worst_case_additional_cost==3
assert plan.branches["B"].kind=="ACT"
assert plan.branches["A"].kind=="PROBE"
assert plan.branches["A"].probe_id=="fine_split"
assert_plan_safe(plan,100,worlds,[p1,p2])

for w in worlds:
    assert w.true_debt < 100

# Unsound context certificate is rejected when reached.
bad=CertifiedAdaptiveProbe(
    "bad",1,
    {"w1":"Q","w2":"Q","w3":"R","w4":"R"},
    {},
    {"w1,w2,w3,w4::Q":80,"w1,w2,w3,w4::R":80},
    "bad-authority",
)
try:
    plan_guaranteed_act(reserve=100,baseline_upper_bound=130,worlds=worlds,probes=[bad])
except AdaptiveProofError as e:
    assert str(e)=="UNSOUND_CONTEXT_CERTIFICATE"
else:
    raise AssertionError("unsound context certificate accepted")

# If one possible world is truly unsafe, the safe tree can isolate it but cannot ACT on it.
unsafe_worlds=[FiniteWorld("s1",90),FiniteWorld("s2",120)]
q=CertifiedAdaptiveProbe(
    "q",1,
    {"s1":"L","s2":"H"},
    {"L":90,"H":120},
    None,
    "authority-q",
)
blocked=plan_guaranteed_act(
    reserve=100,baseline_upper_bound=130,worlds=unsafe_worlds,probes=[q])
assert blocked.kind=="REFUSE"
assert_plan_safe(blocked,100,unsafe_worlds,[q])

print("ADAPTIVE_PROOF_ACQUISITION_V2_TESTS: PASS")
