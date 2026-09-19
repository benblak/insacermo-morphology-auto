import hashlib
import itertools
import os
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path

MATHLIB_REPO = "https://github.com/leanprover-community/mathlib4.git"
MATHLIB_COMMIT = "dec5b2b780537b6eaf7f5e5f000c12f7387fb24d"
TARGET_COUNT = 12
MAX_BUNDLE = 3
DAMAGE_RANKS = [1, 25, 100]   # ranks by direct dependent count
BUDGETS = [0, 1, 2, 3]

root = Path(os.environ.get("MATHLIB_ROOT", "/tmp/mathlib4"))

if not root.exists():
    subprocess.run(
        ["git", "clone", "--filter=blob:none", "--no-checkout", MATHLIB_REPO, str(root)],
        check=True,
    )
subprocess.run(["git", "-C", str(root), "fetch", "--depth", "1", "origin", MATHLIB_COMMIT], check=True)
subprocess.run(["git", "-C", str(root), "checkout", "--detach", MATHLIB_COMMIT], check=True)

actual = subprocess.check_output(
    ["git", "-C", str(root), "rev-parse", "HEAD"], text=True
).strip()
assert actual == MATHLIB_COMMIT, (actual, MATHLIB_COMMIT)

mathlib_dir = root / "Mathlib"
files = sorted(mathlib_dir.rglob("*.lean"))
assert files, "no Mathlib Lean files found"

def module_name(path: Path) -> str:
    rel = path.relative_to(root).with_suffix("")
    return ".".join(rel.parts)

modules = {module_name(p): p for p in files}
module_set = set(modules)

import_re = re.compile(r"^\s*(?:(?:public|private)\s+)?import\s+([A-Za-z0-9_'.]+)\s*$")

def strip_lean_comments(source: str) -> str:
    # Remove nested /- ... -/ comments and -- comments before parsing imports.
    # This is a parser correction only; target/damage rules are unchanged.
    out = []
    i = 0
    depth = 0
    while i < len(source):
        if i + 1 < len(source) and source[i:i+2] == "/-":
            depth += 1
            i += 2
            continue
        if depth and i + 1 < len(source) and source[i:i+2] == "-/":
            depth -= 1
            i += 2
            continue
        if depth:
            i += 1
            continue
        if i + 1 < len(source) and source[i:i+2] == "--":
            j = source.find("\n", i)
            if j == -1:
                break
            out.append("\n")
            i = j + 1
            continue
        out.append(source[i])
        i += 1
    return "".join(out)

imports = {}
for mod, path in modules.items():
    deps = set()
    source = path.read_text(encoding="utf-8", errors="replace")
    for line in strip_lean_comments(source).splitlines():
        m = import_re.match(line)
        if m:
            dep = m.group(1)
            if dep in module_set:
                deps.add(dep)
    imports[mod] = deps

# Verify acyclicity of the parsed internal import graph.
state = {}
def visit(u):
    s = state.get(u, 0)
    if s == 1:
        raise AssertionError(f"cycle detected at {u}")
    if s == 2:
        return
    state[u] = 1
    for v in imports[u]:
        visit(v)
    state[u] = 2

for m in modules:
    visit(m)

# Direct dependent counts are outcome-independent graph statistics.
dependents = Counter()
for u, deps in imports.items():
    for v in deps:
        dependents[v] += 1

eligible_damage = [
    m for m in module_set
    if dependents[m] > 0
    and not m.startswith("Mathlib.Tactic")
    and not m.startswith("Mathlib.Util")
]
ranked_damage = sorted(
    eligible_damage,
    key=lambda m: (-dependents[m], m),
)
print("DESIGN_DIAGNOSTIC_PARSED_MODULES", len(modules))
print("DESIGN_DIAGNOSTIC_PARSED_IMPORT_EDGES", sum(len(v) for v in imports.values()))
print("DESIGN_DIAGNOSTIC_NONZERO_DEPENDENT_MODULES", sum(dependents[m] > 0 for m in module_set))
print("DESIGN_DIAGNOSTIC_ELIGIBLE_DAMAGE", len(ranked_damage))
print("DESIGN_DIAGNOSTIC_TOP_COUNTS", " ".join(str(dependents[m]) for m in ranked_damage[:10]))
assert len(ranked_damage) >= max(DAMAGE_RANKS)
damages = [ranked_damage[r - 1] for r in DAMAGE_RANKS]

# Blind target rule: choose leaves (no module depends on them) by SHA256(module name).
leaf_modules = [
    m for m in module_set
    if dependents[m] == 0
    and not m.startswith("Mathlib.Tactic")
    and not m.startswith("Mathlib.Util")
    and not m.endswith(".Defs")
]
assert len(leaf_modules) >= TARGET_COUNT

def digest_key(name):
    return hashlib.sha256(name.encode("utf-8")).hexdigest()

targets = sorted(leaf_modules, key=lambda m: (digest_key(m), m))[:TARGET_COUNT]

# Exact transitive closure in the parsed import DAG.
closure_cache = {}
def closure(m):
    if m in closure_cache:
        return closure_cache[m]
    c = set()
    for d in imports[m]:
        c.add(d)
        c.update(closure(d))
    closure_cache[m] = frozenset(c)
    return closure_cache[m]

for m in modules:
    closure(m)

required_damage = {
    t: frozenset(d for d in damages if d == t or d in closure(t))
    for t in targets
}

bundles = []
for k in range(1, MAX_BUNDLE + 1):
    bundles.extend(itertools.combinations(targets, k))

def bundle_required_damage(bundle):
    s = set()
    for t in bundle:
        s.update(required_damage[t])
    return frozenset(s)

# A repair action restores one damaged import module. Depth is the minimal number
# of such restorations required for all modules in the contract bundle to be
# structurally buildable with respect to the parsed import graph.
def depth(bundle):
    req = bundle_required_damage(bundle)
    for b in BUDGETS:
        for restored in itertools.combinations(damages, b):
            if req <= set(restored):
                return b
    return None

depths = {b: depth(b) for b in bundles}
assert all(d is not None for d in depths.values())

single_depth = {t: depths[(t,)] for t in targets}
joint_escalation = [
    b for b in bundles
    if len(b) >= 2 and depths[b] > max(single_depth[t] for t in b)
]

def safe_at(H):
    return {b for b, d in depths.items() if d <= H}

def minimal_obstructions(H):
    safe = safe_at(H)
    obs = []
    for b in bundles:
        if b in safe:
            continue
        proper_ok = True
        for r in range(1, len(b)):
            for sub in itertools.combinations(b, r):
                if sub not in safe:
                    proper_ok = False
                    break
            if not proper_ok:
                break
        if proper_ok:
            obs.append(b)
    return obs

hist = Counter(depths.values())

print("INSACERMO_POSTFREEZE_MATHLIB_REPAIR_GEOMETRY_BLIND_V1")
print("STATUS BLIND_CONFIRMATORY_POSTFREEZE")
print("MATHLIB_COMMIT", MATHLIB_COMMIT)
print("PARSED_MODULES", len(modules))
print("PARSED_IMPORT_EDGES", sum(len(v) for v in imports.values()))
print("ACYCLIC_IMPORT_GRAPH YES")
print("TARGET_RULE SHA256_FIRST_12_LEAF_MODULES")
print("DAMAGE_RULE DIRECT_DEPENDENT_RANKS", " ".join(map(str, DAMAGE_RANKS)))
print("TARGET_COUNT", len(targets))
print("DAMAGE_COUNT", len(damages))
print("CATALOGUE_BUNDLES", len(bundles))
print("MAX_BUNDLE", MAX_BUNDLE)
print("SEMANTICS structural import-availability repair geometry; not theorem runtime and not proof-search time")

for i, d in enumerate(damages, 1):
    print("DAMAGE", i, d, "DIRECT_DEPENDENTS", dependents[d])

for i, t in enumerate(targets, 1):
    req = sorted(required_damage[t])
    print(
        "TARGET", i, t,
        "SINGLE_DEPTH", single_depth[t],
        "REQUIRES", "|".join(req) if req else "NONE",
    )

print("REPAIR_DEPTH_HIST", " ".join(f"D{k}:{hist[k]}" for k in sorted(hist)))
print("JOINT_ESCALATION_COUNT", len(joint_escalation))
for H in BUDGETS:
    safe = safe_at(H)
    obs = minimal_obstructions(H)
    print(
        "HORIZON", H,
        "SAFE", len(safe),
        "FAILED", len(bundles) - len(safe),
        "MINIMAL_OBSTRUCTIONS", len(obs),
        "MIN_OBS_SIZE1", sum(len(b) == 1 for b in obs),
        "MIN_OBS_SIZE2", sum(len(b) == 2 for b in obs),
        "MIN_OBS_SIZE3", sum(len(b) == 3 for b in obs),
    )

if joint_escalation:
    ex = joint_escalation[0]
    print(
        "JOINT_ESCALATION_WITNESS",
        " || ".join(ex),
        "BUNDLE_DEPTH", depths[ex],
        "MAX_SINGLE_DEPTH", max(single_depth[t] for t in ex),
    )

print("RESULT COMPLETE")
