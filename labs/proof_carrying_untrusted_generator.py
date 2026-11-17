#!/usr/bin/env python3
"""Build candidate Lean proofs from an UNTRUSTED Python XOR discovery transcript.
Lean separately checks every observed basis label and all-input algebraic equivalence.
Original C3/MAX TOTAL kernel unchanged. Does not prove arbitrary oracle global truth.
"""
from __future__ import annotations
import argparse,json,hashlib,itertools
from pathlib import Path
N=24
BASIS=[0]+[1<<i for i in range(N)]+[(1<<i)|(1<<j) for i in range(N) for j in range(i+1,N)]
assert len(BASIS)==301 and len(set(BASIS))==301

def xor(parts):
    expr="false"
    for p in parts:expr=f"({expr} != {p})"
    return expr
def parity(mask):
    return xor([f"(x.getLsbD {i})" for i in range(N) if (mask>>i)&1])
def polynomial(rec):
    return xor((["true"] if rec["constant"] else [])+
       [parity(rec["linear"])]+[f"((x.getLsbD {i}) && (x.getLsbD {j}))" for i,j in rec["pairs"]])
def transported(rec):
    cand=rec["candidate"]
    a,b,c,d,e=[parity(t) for t in cand["coordinates"]]
    return xor((["true"] if cand["output_flip"] else [])+
      [a,b,c,d,e,f"({a} && {b})",f"({c} && {d})"])
def generate(seal_path,proof_path,attack="none"):
    source=Path(seal_path);seal=json.loads(source.read_text())
    cases=[r for r in seal["sources"]+seal["targets"]
       if r["candidate"]["status"]=="QUADRATIC_FIVE_COORDINATE_CANDIDATE"]
    assert len(cases)==7 and len(set(r["name"] for r in cases))==7
    # Deep-copy so mutation never affects source or original oracle transcript.
    cases=json.loads(json.dumps(cases))
    if attack=="coordinate":cases[0]["candidate"]["coordinates"][0]^=1
    lines=[
      "import Std.Tactic.BVDecide",
      "set_option maxRecDepth 25000",
      "set_option maxHeartbeats 20000000",
      "namespace InsacermoProofCarryingTranscripts",
      "/- CONDITIONAL model proof: the 301 source labels are checked as stated.",
      "   An independent observer must verify those labels against real oracle replies.",
      "   Even 301 basis labels do not prove an unrestricted oracle quadratic. -/",
      "def basis : Array Nat := #["+(", ".join(str(x) for x in BASIS))+"]"]
    labels_hashes={}
    for index,rec in enumerate(cases):
        name=rec["name"]
        assert name.replace("_","").isalnum()
        samples=dict(rec["transcript"]["rows"])
        assert all(x in samples for x in BASIS)
        labels=[int(samples[x]) for x in BASIS]
        if attack=="label" and index==0:labels[0]^=1
        labels_hashes[name]=hashlib.sha256(bytes(labels)).hexdigest()
        label_lit=", ".join("true" if b else "false" for b in labels)
        lines += [
          f"def {name}_reported : Array Bool := #[{label_lit}]",
          f"def {name}_quadratic (x : BitVec 24) : Bool := {polynomial(rec)}",
          f"def {name}_transported (x : BitVec 24) : Bool := {transported(rec)}",
          f"theorem {name}_reported_size : {name}_reported.size = 301 := by decide",
          *[f"theorem {name}_label_{i:03d} : {name}_quadratic (BitVec.ofNat 24 {BASIS[i]}) = {str(bool(labels[i])).lower()} := by decide" for i in range(301)],
          f"theorem {name}_xor_coordinates_equal_quadratic_for_all_x (x : BitVec 24) :",
          f"  {name}_quadratic x = {name}_transported x := by",
          f"  unfold {name}_quadratic {name}_transported",
          "  bv_decide"
        ]
    lines.extend([
      "/-- Finite observations cannot rule out a point exception outside their domain. -/",
      "def flippedAt (f : Nat → Bool) (exception x : Nat) : Bool :=",
      "  if x = exception then !(f x) else f x",
      "theorem hidden_exception_is_indistinguishable",
      "  (f : Nat → Bool) (seen : List Nat) (exception : Nat)",
      "  (unseen : exception ∉ seen) :",
      "  (∀ x ∈ seen, flippedAt f exception x = f x) ∧",
      "  flippedAt f exception exception ≠ f exception := by",
      "  constructor",
      "  · intro x hx",
      "    have hne : x ≠ exception := by",
      "      intro h; apply unseen; simpa [h] using hx",
      "    simp [flippedAt, hne]",
      "  · cases hv : f exception <;> simp [flippedAt, hv]",
      "end InsacermoProofCarryingTranscripts",""])
    target=Path(proof_path);target.write_text("\n".join(lines))
    summary={"status":"GENERATED_NOT_YET_VERIFIED","source_seal_sha256":hashlib.sha256(source.read_bytes()).hexdigest(),
      "lean_source_sha256":hashlib.sha256(target.read_bytes()).hexdigest(),
      "attack":attack,"models":len(cases),"recorded_basis_observations":len(cases)*301,
      "model_names":[r["name"] for r in cases],"labels_hashes":labels_hashes,
      "scope":"2107 stated oracle labels plus 7 all-24-bit POLYNOMIAL EQUIVALENCES; not arbitrary oracle global correctness"}
    target.with_suffix(".json").write_text(json.dumps(summary,indent=2)+"\n")
    print("EVIDENCE_CANDIDATE",attack,summary["lean_source_sha256"],flush=True)
if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("sealed");p.add_argument("output")
    p.add_argument("--attack",choices=("none","label","coordinate"),default="none")
    a=p.parse_args();generate(a.sealed,a.output,a.attack)
