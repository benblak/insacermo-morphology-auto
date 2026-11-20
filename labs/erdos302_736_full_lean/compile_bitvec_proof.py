#!/usr/bin/env python3
"""Generate a Lean 4 bitvector upper-bound proof attempt for n=736.
No SciPy dual bound is imported. Every 736-bit omission assignment is quantified.
Lean bv_decide checks propositional validity by bitblasting and proof verification.
"""
from pathlib import Path
import os
OUT=Path(os.environ.get("ERDOS736_OUT","/tmp/erdos736-full-lean"))
OUT.mkdir(parents=True,exist_ok=True)
N=736
triples=[(a,b,c) for c in range(2,N+1) for b in range(1,c)
  if (b*c)%(b+c)==0
  for a in [b*c//(b+c)] if 0<a<b]
assert len(triples)==742
active=sorted({v for t in triples for v in t})
assert len(active)==416
set_option_note='Global 736-bit bound; solver time explicitly raised to 600 seconds'
header='''import Lean

/-!
INSACERMO Erdős #302: global upper bound using a 736-bit finite assignment.
A bit at (v-1) = TRUE means v is omitted.
Every triple a<b<c obeying a(b+c)=bc must contain an omitted vertex.
An admissible 610-element subset has <=126 omissions.

If Lean's bv_decide compiles, SAT proof is checked by Lean.
No C3 engine modifications. No assumption on OEIS f(731).
-/
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000000
set_option sat.timeout 600
namespace INSACERMO.Erdos736Full

'''
def bit(v):return f"(x.getLsbD {v-1})"
conds=[f"({bit(a)} || {bit(b)} || {bit(c)})" for a,b,c in triples]
adds=[f"(if {bit(v)} then (1 : BitVec 10) else 0)" for v in active]
body=header
body+="def covered (x : BitVec 736) : Bool :=\n  " + "\n  && ".join(conds) + "\n\n"
body+="def excludedActive (x : BitVec 736) : BitVec 10 :=\n  "+ "\n  + ".join(["(0 : BitVec 10)"]+adds)+"\n\n"
body+="theorem cannot_cover_with_only_126_exclusions (x : BitVec 736) :\n"
body+="    covered x = true → ((excludedActive x) < (127 : BitVec 10)) = false := by\n"
body+="  intro h\n  unfold covered at h\n  unfold excludedActive\n  bv_decide\n\nend INSACERMO.Erdos736Full\n"
path=OUT/"Erdos736SAT.lean"
path.write_text(body)
print('LEAN_SOURCE',path,'bytes',path.stat().st_size,'triples',len(triples),'active',len(active))
