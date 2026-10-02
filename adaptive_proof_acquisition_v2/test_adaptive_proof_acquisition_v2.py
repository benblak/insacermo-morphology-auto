from adaptive_proof_acquisition_v2 import *

worlds=[
    FiniteWorld("w1",90),
    FiniteWorld("w2",85),
    FiniteWorld("w3",80),
    FiniteWorld("w4",75),
]

# Coarse first probe: one branch closes immediately; the other remains sound but too loose.
p1=CertifiedAdaptiveProbe(
    "coarse_split",1,
    {"w1":"A","w2":"A","w3":"B","w4":"B"},
    {"A":110,"B":90},
    "authority-coarse",
)

# Follow-up probe only becomes useful on branch A. Its certificates are sound there.
# For worlds in B the outcomes are present too because the finite soundness checker requires
# a total map; those branches are never reached by the optimal plan.
p2=CertifiedAdaptiveProbe(
    "fine_split",2,
    {"w1":"X","w2":"Y","w3":"X","w4":"Y"},
    {"X":90,"Y":85},
    "authority-fine",
)

for p in (p1,p2):
    validate_probe_soundness(worlds,p)

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

# Every finite world is truly safe (<100), yet the baseline bound 130 blocks ACT.
# Acquisition recovers ACT by tightening the proof, not by changing the world.
for w in worlds:
    assert w.true_debt < 100

# Unsound certificates are rejected.
bad=CertifiedAdaptiveProbe(
    "bad",1,
    {"w1":"Q","w2":"Q","w3":"R","w4":"R"},
    {"Q":80,"R":80},
    "bad-authority",
)
try:
    validate_probe_soundness(worlds,bad)
except AdaptiveProofError as e:
    assert str(e)=="UNSOUND_OUTCOME_CERTIFICATE"
else:
    raise AssertionError("unsound certificate accepted")

# If one possible world is truly unsafe and no probe can remove it with a sound ACT certificate,
# guaranteed ACT is impossible and the planner fails closed.
unsafe_worlds=[FiniteWorld("s1",90),FiniteWorld("s2",120)]
q=CertifiedAdaptiveProbe(
    "q",1,
    {"s1":"L","s2":"H"},
    {"L":90,"H":120},
    "authority-q",
)
blocked=plan_guaranteed_act(
    reserve=100,baseline_upper_bound=130,worlds=unsafe_worlds,probes=[q])
assert blocked.kind=="REFUSE"
assert_plan_safe(blocked,100,unsafe_worlds,[q])

print("ADAPTIVE_PROOF_ACQUISITION_V2_TESTS: PASS")
