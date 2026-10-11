from online_debt_v1 import *
NOW="2026-10-02T08:00:00+00:00"; C="contract"; O="observer"
P=[
 AuthorityPolicy("current","CURRENT_CERTIFIED_BOUND",C,O),
 AuthorityPolicy("delayed","DELAYED_EXACT_PLUS_GROWTH_CAP",C,O,max_growth_per_step=2,max_age_steps=5),
 AuthorityPolicy("probe","FRESH_PROBE_BOUND",C,O,max_age_steps=1),
 AuthorityPolicy("c1","CURRENT_CERTIFIED_BOUND",C,O,debt_scope="COMPONENTS",component="sensor"),
 AuthorityPolicy("c2","CURRENT_CERTIFIED_BOUND",C,O,debt_scope="COMPONENTS",component="regime"),
]
v=DebtVerifier(P); checks=[]
def claim(a,b,w,r,scope="TOTAL",component=None,contract=C):
 return DebtClaim(a,"A",contract,O,scope,b,"2026-10-02T07:59:00+00:00","E0",r,w,None,component)
def reject(code,f):
 try: f()
 except DebtVerificationError as e:
  assert str(e)==code,(str(e),code); return
 raise AssertionError(code)

b=v.verify(claim("current",4,{"current_upper_bound":4},"CURRENT_CERTIFIED_BOUND"),now=NOW); assert b.upper_bound==4; checks.append("current")
reject("CLAIMED_BOUND_NOT_RECOMPUTABLE",lambda:v.verify(claim("current",3,{"current_upper_bound":4},"CURRENT_CERTIFIED_BOUND"),now=NOW)); checks.append("tamper")
reject("CONTRACT_SCOPE_MISMATCH",lambda:v.verify(claim("current",4,{"current_upper_bound":4},"CURRENT_CERTIFIED_BOUND",contract="bad"),now=NOW)); checks.append("contract")
d=v.verify(claim("delayed",9,{"exact_debt_at_source":3,"source_step":10,"target_step":13},"DELAYED_EXACT_PLUS_GROWTH_CAP"),now=NOW); assert d.upper_bound==9; checks.append("delayed-growth")
reject("SOURCE_TOO_OLD",lambda:v.verify(claim("delayed",15,{"exact_debt_at_source":3,"source_step":10,"target_step":16},"DELAYED_EXACT_PLUS_GROWTH_CAP"),now=NOW)); checks.append("old")
p=v.verify(claim("probe",5,{"probe_upper_bound":5,"age_steps":1},"FRESH_PROBE_BOUND"),now=NOW); assert p.upper_bound==5; checks.append("probe")
reject("PROBE_TOO_OLD",lambda:v.verify(claim("probe",5,{"probe_upper_bound":5,"age_steps":2},"FRESH_PROBE_BOUND"),now=NOW)); checks.append("probe-old")
c1=v.verify(claim("c1",2,{"current_upper_bound":2},"CURRENT_CERTIFIED_BOUND","COMPONENTS","sensor"),now=NOW)
c2=v.verify(claim("c2",3,{"current_upper_bound":3},"CURRENT_CERTIFIED_BOUND","COMPONENTS","regime"),now=NOW)
s=sum_components([c1,c2]); assert s.upper_bound==5; checks.append("sum-components")
w=no_free_debt_counterexample(reserve=10,observation="same",low_debt=4,high_debt=12,observation_only_bound=4)
assert w["act_permitted_from_observation_only_bound"] and not w["bound_sound_in_high_world"] and w["unsafe_hidden_world_exists"]; checks.append("no-free-debt")
print("CERTIFIED_ONLINE_DEBT_TESTS: PASS",len(checks))
