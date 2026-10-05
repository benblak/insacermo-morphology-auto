from information_price_runtime_v1 import *

def obs(p,w): return w["obs"][p]
def act(w): return w["action"]

def test_valid_and_tamper():
    worlds=[
      {"obs":{"p":0,"q":0},"action":"A"},
      {"obs":{"p":0,"q":1},"action":"A"},
      {"obs":{"p":1,"q":0},"action":"B"},
    ]
    cert=make_certificate(worlds,0,["p"],obs,act)
    assert cert.price==1
    assert verify_certificate(worlds,0,cert.probes,obs,act,cert.action,cert.outcomes,cert.price).valid
    assert not verify_certificate(worlds,0,cert.probes,obs,act,"B",cert.outcomes,cert.price).valid
    assert not verify_certificate(worlds,0,cert.probes,obs,act,cert.action,(9,),cert.price).valid
    assert not verify_certificate(worlds,0,cert.probes,obs,act,cert.action,cert.outcomes,2).valid

def test_conflict_forces_refuse():
    worlds=[
      {"obs":{"p":0},"action":"A"},
      {"obs":{"p":0},"action":"B"},
    ]
    r=classify_with_certificate(worlds,0,["p"],obs,act)
    assert r["verdict"]=="REFUSE"
    assert not verify_certificate(worlds,0,["p"],obs,act).valid

def test_irredundancy():
    worlds=[
      {"obs":{"p":0,"q":0,"r":0},"action":"A"},
      {"obs":{"p":1,"q":0,"r":0},"action":"B"},
      {"obs":{"p":0,"q":1,"r":0},"action":"B"},
    ]
    cert=irredundant_certificate(worlds,0,["p","q","r"],obs,act)
    assert cert is not None
    assert set(cert.probes)=={"p","q"}
    assert cert.price==2
    for p in cert.probes:
        trial=[z for z in cert.probes if z!=p]
        assert not verify_certificate(worlds,0,trial,obs,act).valid

if __name__=="__main__":
    test_valid_and_tamper()
    test_conflict_forces_refuse()
    test_irredundancy()
    print("INFORMATION_PRICE_RUNTIME_V1: PASS")
