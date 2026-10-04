from pathlib import Path
import sys

scenario = sys.argv[1]
src = Path("erdos302_f736_bv_kernel/Erdos302F736BV.lean").read_text()
prefix = "\n".join(src.splitlines()[:770]) + "\n"

base = [
    "(h735 : x.getLsbD 734 = true)",
    "(h736 : x.getLsbD 735 = true)",
]

cases735 = {
    "m294": ["(h294 : x.getLsbD 293 = false)"],
    "p294": [
        "(h294 : x.getLsbD 293 = true)",
        "(h210 : x.getLsbD 209 = false)",
        "(h490 : x.getLsbD 489 = false)",
    ],
}

cases736 = {
    "m207_m224": [
        "(h207 : x.getLsbD 206 = false)",
        "(h224 : x.getLsbD 223 = false)",
    ],
    "m207_m322": [
        "(h207 : x.getLsbD 206 = false)",
        "(h322 : x.getLsbD 321 = false)",
    ],
    "m288_m224": [
        "(h288 : x.getLsbD 287 = false)",
        "(h224 : x.getLsbD 223 = false)",
    ],
    "m288_m322": [
        "(h288 : x.getLsbD 287 = false)",
        "(h322 : x.getLsbD 321 = false)",
    ],
}

left, right = scenario.split("__", 1)
assumptions = base + cases735[left] + cases736[right]
thm = "endpoint_pair_probe_" + scenario
extra = "\n    ".join(assumptions)

body = f"""
/-- Critical f(736) probe: both new endpoints are selected. -/
theorem {thm} (x : BitVec 736)
    (h : admissible736Bits x = true)
    {extra} :
    x.cpop < (610#736) := by
  simp only [admissible736Bits, tripleOK] at h
  bv_decide (config := {{ timeout := 300 }})

#print axioms {thm}

end Erdos302F736BV
"""

Path("erdos302_f736_bv_kernel/SplitProbe.lean").write_text(prefix + body)
print(thm)
