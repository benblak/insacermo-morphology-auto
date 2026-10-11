from temporal_runtime_v1 import *
def ev(x,epoch="E0",cert=True,until=None):
    return DebtEvidence("A",x,"c","o","test","2026-10-02T05:00:00+00:00",epoch,until,cert)
base={"verdict":"ACT","selected_action":"A"}
r=Runtime("c","o")
a=r.evaluate(base_receipt=base,signature=[1],rho0=10,evidence=ev(4),now="2026-10-02T05:30:00+00:00")
assert a["temporal_verdict"]=="ACT" and a["residual_reserve"]==6 and Runtime.verify(a)["valid"]
b=r.evaluate(base_receipt=base,signature=[1],rho0=10,evidence=ev(10),now="2026-10-02T05:31:00+00:00")
assert b["temporal_verdict"]=="PROBE"
c=Runtime("c","o").evaluate(base_receipt=base,signature=[1],rho0=10,evidence=None,now="2026-10-02T05:31:00+00:00")
assert c["temporal_verdict"]=="PROBE"
d=Runtime("c","o").evaluate(base_receipt=base,signature=[1],rho0=10,evidence=ev(2,cert=False),now="2026-10-02T05:31:00+00:00")
assert d["temporal_verdict"]=="VALIDITY_REFUSE"
rr=Runtime("c","o")
assert rr.evaluate(base_receipt=base,signature=[1],rho0=20,evidence=ev(8),now="2026-10-02T05:31:00+00:00")["temporal_verdict"]=="ACT"
assert rr.evaluate(base_receipt=base,signature=[1],rho0=20,evidence=ev(7),now="2026-10-02T05:32:00+00:00")["temporal_verdict"]=="VALIDITY_REFUSE"
assert rr.evaluate(base_receipt=base,signature=[1],rho0=20,evidence=ev(3,"E1"),now="2026-10-02T05:33:00+00:00")["temporal_verdict"]=="ACT"
fr=FractureRegistry(); assert fr.record([1,2],"0",{"t":0}) is None; w=fr.record([1,2],"1",{"t":1}); assert w
f=Runtime("c","o").evaluate(base_receipt=base,signature=[1,2],rho0=100,evidence=ev(0),now="2026-10-02T05:31:00+00:00",fracture=w,probe=False,repair=True)
assert f["temporal_verdict"]=="REPAIR"
bad=dict(a);bad["residual_reserve"]=999;assert not Runtime.verify(bad)["valid"]
print("TEMPORAL_RUNTIME_UNIT_TESTS: PASS")
