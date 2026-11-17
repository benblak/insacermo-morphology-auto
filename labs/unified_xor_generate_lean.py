#!/usr/bin/env python3
"""Generate *universal* Lean equality for each discovered 24-bit quadratic model.
Output fails closed if Lean cannot prove identity of XOR masks vs ANF for ALL x.
No assertion that inaccessible oracle has this degree; rare exception refutes that.
"""
import json,sys,re,hashlib
from pathlib import Path

def xor(parts):
    if not parts:return "false"
    expr=parts[0]
    for p in parts[1:]:expr=f"({expr} != {p})"
    return expr
def bit(i):return f"(x.getLsbD {i})"
def parity(mask):
    return xor([bit(i) for i in range(24) if mask&(1<<i)])
def compound(masks,flip):
    a,b,c,d,e=[parity(v) for v in masks]
    return xor(["true" if flip else "false",a,b,c,d,e,f"({a} && {b})",f"({c} && {d})"])
def quadratic(r):
    pieces=["true" if r['constant'] else "false",parity(r['linear'])]
    pieces += [f"({bit(i)} && {bit(j)})" for i,j in r['pairs']]
    return xor(pieces)
def generate(seal,out):
    seal=Path(seal);out=Path(out)
    models=json.loads(seal.read_text())
    items=[r for r in models['sources']+models['targets']
        if r['candidate']['status']=='QUADRATIC_FIVE_COORDINATE_CANDIDATE']
    assert len(items)==7 and len({r['name'] for r in items})==7
    lines=["import Std.Tactic.BVDecide","set_option maxRecDepth 20000",
       "set_option maxHeartbeats 10000000",
       "namespace InsacermoXorVerifiedAll24BitInputs",
       "/- Each proof is conditional on the given quadratic ANF being the",
       "actual law. For an arbitrary oracle, unseen exceptions remain possible. -/"]
    for rec in items:
        name=rec['name']
        assert re.fullmatch(r'[a-z_0-9]+',name)
        transformed=compound(rec['candidate']['coordinates'],rec['candidate']['output_flip'])
        anf=quadratic(rec)
        lines += [f"theorem {name}_all_24_bit_inputs (x : BitVec 24) :",
           f"  ({transformed}) = ({anf}) := by",
           "  bv_decide",""]
    lines.append("end InsacermoXorVerifiedAll24BitInputs")
    out.write_text("\n".join(lines)+"\n")
    receipt={"proof_sha256":hashlib.sha256(out.read_bytes()).hexdigest(),
       "source_seal_sha256":hashlib.sha256(seal.read_bytes()).hexdigest(),
       "verified_models":[r['name'] for r in items],
       "domain":2**24,"scope":"IDENTITY BETWEEN TWO DECLARED QUADRATIC POLYNOMIALS, NOT UNKNOWN ORACLE"}
    out.with_suffix(".json").write_text(json.dumps(receipt,indent=2)+"\n")
    print("GENERATED_7_UNIVERSAL_QUADRATIC_IDENTITIES",receipt["proof_sha256"],flush=True)
if __name__=="__main__":generate(sys.argv[1],sys.argv[2])
