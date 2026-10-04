#!/usr/bin/env python3
from pathlib import Path
import sys

N = 734

def triples_upto(n):
    out = []
    for b in range(1, n + 1):
        for c in range(b + 1, n + 1):
            num = b * c
            den = b + c
            q, r = divmod(num, den)
            if r == 0 and 1 <= q < b:
                out.append((q, b, c))
    return out

triples = triples_upto(N)
assert len(triples) == 738, len(triples)

parent = list(range(N + 1))

def find(x):
    while parent[x] != x:
        parent[x] = parent[parent[x]]
        x = parent[x]
    return x

def union(a, b):
    ra, rb = find(a), find(b)
    if ra != rb:
        parent[rb] = ra

for a, b, c in triples:
    union(a, b)
    union(a, c)

root = find(322)
core = [v for v in range(1, N + 1) if find(v) == root]
core_set = set(core)
core_triples = [t for t in triples if t[0] in core_set]
assert len(core) == 342, len(core)
assert len(core_triples) == 705, len(core_triples)
assert 224 in core_set and 322 in core_set

idx = {v: i for i, v in enumerate(core)}
scenario = sys.argv[1]
if scenario not in ("omit224", "omit322"):
    raise SystemExit("scenario must be omit224 or omit322")
omit = 224 if scenario == "omit224" else 322

clauses = []
for a, b, c in core_triples:
    clauses.append(f"  tripleOK x {idx[a]} {idx[b]} {idx[c]}")
body = " &&\n".join(clauses)

thm = f"core342_{scenario}"
src = f'''import Std
import Std.Tactic.BVDecide

/-!
Erdős 302 — exact hard-core reduction at n=734.
Generated deterministically from a(b+c)=bc.
The connected component containing vertex 322 has 342 vertices and 705 forbidden triples.
All other components are handled separately by finite kernel checks.
-/

namespace Erdos302F736Core342

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def tripleOK (x : BitVec 342) (i j k : Nat) : Bool :=
  !(x.getLsbD i && x.getLsbD j && x.getLsbD k)

def admissibleCore (x : BitVec 342) : Bool :=
{body}

/-- If vertex {omit} is omitted, the hard component contains at most 239 selected vertices. -/
theorem {thm} (x : BitVec 342)
    (h : admissibleCore x = true)
    (homit : x.getLsbD {idx[omit]} = false) :
    x.cpop < (240#342) := by
  simp only [admissibleCore, tripleOK] at h
  bv_decide (config := {{ timeout := 300, acNf := true }})

#print axioms {thm}

end Erdos302F736Core342
'''
Path("erdos302_f736_bv_kernel/Core342.lean").write_text(src)
print(f"CORE_VERTICES={len(core)} CORE_TRIPLES={len(core_triples)} OMIT={omit} INDEX={idx[omit]}")
