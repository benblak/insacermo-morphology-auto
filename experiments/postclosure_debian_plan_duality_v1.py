import hashlib
import itertools
import lzma
import re
import subprocess
import urllib.request
from pathlib import Path

RELEASE_URL = "https://deb.debian.org/debian/dists/trixie/Release"
PACKAGES_URL = "https://deb.debian.org/debian/dists/trixie/main/binary-amd64/Packages.xz"
EXPECTED_VERSION = "13.7"
EXPECTED_CODENAME = "trixie"
TARGETS = ["curl", "git", "nginx", "postgresql", "imagemagick", "ffmpeg", "rsync", "sqlite3"]
MAX_BUNDLE = 3
PLAN_BUDGET = 1

ROOT = Path("debian_plan_duality_work")
ROOT.mkdir(exist_ok=True)

def download(url):
    with urllib.request.urlopen(url, timeout=120) as r:
        return r.read()

release_raw = download(RELEASE_URL)
release_text = release_raw.decode("utf-8")
release_sha256 = hashlib.sha256(release_raw).hexdigest()

def field_value(name):
    m = re.search(rf"(?m)^{re.escape(name)}:\s*(.+)$", release_text)
    if not m:
        raise RuntimeError(f"missing Release field {name}")
    return m.group(1).strip()

assert field_value("Version") == EXPECTED_VERSION
assert field_value("Codename") == EXPECTED_CODENAME

sha_block = release_text.split("SHA256:", 1)[1]
pkg_match = re.search(
    r"(?m)^\s*([0-9a-f]{64})\s+(\d+)\s+main/binary-amd64/Packages\.xz\s*$",
    sha_block,
)
if not pkg_match:
    raise RuntimeError("Packages.xz SHA256 not found in Release")
expected_pkg_sha256, expected_pkg_size = pkg_match.group(1), int(pkg_match.group(2))

packages_xz = download(PACKAGES_URL)
actual_pkg_sha256 = hashlib.sha256(packages_xz).hexdigest()
assert actual_pkg_sha256 == expected_pkg_sha256
assert len(packages_xz) == expected_pkg_size
packages_text = lzma.decompress(packages_xz).decode("utf-8")

def parse_stanzas(text):
    out = []
    for raw in text.strip().split("\n\n"):
        fields = {}
        current = None
        for line in raw.splitlines():
            if line.startswith((" ", "\t")) and current:
                fields[current] += "\n" + line
                continue
            if ":" not in line:
                continue
            k, v = line.split(":", 1)
            current = k
            fields[k] = v.strip()
        if "Package" in fields:
            out.append((fields, raw + "\n"))
    return out

stanzas = parse_stanzas(packages_text)
by_name = {fields["Package"]: (fields, raw) for fields, raw in stanzas}
for target in TARGETS:
    assert target in by_name

dep_name_re = re.compile(r"^\s*([a-z0-9][a-z0-9+.-]*)(?::[a-z0-9-]+)?")

def dependency_names(fields):
    names = set()
    for key in ("Pre-Depends", "Depends"):
        value = fields.get(key, "")
        for clause in value.replace("\n", " ").split(","):
            for alt in clause.split("|"):
                m = dep_name_re.match(alt)
                if m:
                    names.add(m.group(1))
    return names

deps = {name: dependency_names(fields) for name, (fields, _) in by_name.items()}

def closure(start):
    seen, stack = set(), [start]
    while stack:
        p = stack.pop()
        if p in seen:
            continue
        seen.add(p)
        for q in deps.get(p, ()):
            if q in by_name and q not in seen:
                stack.append(q)
    return seen

closures = {t: closure(t) for t in TARGETS}
coverage = {}
for name in by_name:
    cov = frozenset(t for t in TARGETS if name in closures[t])
    if cov:
        coverage[name] = cov

def structurally_eligible(name):
    if name in TARGETS:
        return False
    fields = by_name[name][0]
    if fields.get("Essential", "").lower() == "yes":
        return False
    if fields.get("Priority", "").lower() in {"required", "important", "standard"}:
        return False
    k = len(coverage.get(name, ()))
    return 2 <= k < len(TARGETS)

candidates = [p for p in coverage if structurally_eligible(p)]
assert len(candidates) >= 3

c1 = sorted(candidates, key=lambda p: (-len(coverage[p]), p))[0]
remaining = [p for p in candidates if p != c1]
c2 = sorted(
    remaining,
    key=lambda p: (-len(coverage[p] ^ coverage[c1]), -len(coverage[p]), p),
)[0]
remaining = [p for p in remaining if p != c2]
c3 = sorted(
    remaining,
    key=lambda p: (
        -min(len(coverage[p] ^ coverage[c1]), len(coverage[p] ^ coverage[c2])),
        -(len(coverage[p] ^ coverage[c1]) + len(coverage[p] ^ coverage[c2])),
        -len(coverage[p]),
        p,
    ),
)[0]
PERTURB = [c1, c2, c3]

bundles = []
for k in range(1, MAX_BUNDLE + 1):
    bundles.extend(itertools.combinations(TARGETS, k))
assert len(bundles) == 92

contract_name = {b: f"insacermo-contract-{i:03d}" for i, b in enumerate(bundles, 1)}
bundle_of = {v: k for k, v in contract_name.items()}

def repo_for(restored):
    removed = set(PERTURB) - set(restored)
    real_parts = []
    for fields, raw in stanzas:
        if fields["Package"] not in removed:
            real_parts.append(raw.rstrip() + "\n")
    tag = "none" if not restored else "_".join(sorted(restored))
    bg_path = ROOT / ("background_" + tag + ".Packages")
    bg_path.write_text("\n".join(real_parts) + "\n", encoding="utf-8")

    contract_parts = []
    for bundle in bundles:
        name = contract_name[bundle]
        contract_parts.append(
            f"Package: {name}\n"
            f"Version: 1\n"
            f"Architecture: amd64\n"
            f"Depends: {', '.join(bundle)}\n"
            f"Description: INSACERMO synthetic future contract {'+'.join(bundle)}\n"
        )
    fg_path = ROOT / ("contracts_" + tag + ".Packages")
    fg_path.write_text("\n".join(contract_parts) + "\n", encoding="utf-8")
    return bg_path, fg_path

def exact_success_set(restored):
    background, foreground = repo_for(restored)
    cmd = [
        "dose-debcheck",
        "--deb-native-arch=amd64",
        "--failures",
        "--bg=" + str(background),
        str(foreground),
    ]
    p = subprocess.run(cmd, text=True, capture_output=True, timeout=240)
    if p.returncode not in (0, 1):
        raise RuntimeError(
            f"dose-debcheck abnormal exit {p.returncode}\nSTDOUT:\n{p.stdout}\nSTDERR:\n{p.stderr}"
        )
    failed = set(re.findall(r"(?mi)^package:\s*(insacermo-contract-\d+)\s*$", p.stdout))
    assert not (failed - set(bundle_of))
    return {b for b in bundles if contract_name[b] not in failed}

# All restoration subsets are needed to define intact Gamma; budget-1 plans are
# then selected from the same exact solver results.
all_subsets = [
    frozenset(s)
    for r in range(0, len(PERTURB) + 1)
    for s in itertools.combinations(PERTURB, r)
]
success = {s: exact_success_set(s) for s in all_subsets}

full = frozenset(PERTURB)
baseline = success[full]
for t in TARGETS:
    assert (t,) in baseline

Gamma = sorted(baseline, key=lambda b: (len(b), b))
assert Gamma

plans = sorted(
    [s for s in all_subsets if len(s) <= PLAN_BUDGET],
    key=lambda s: (len(s), tuple(sorted(s))),
)
assert len(plans) == 4
plan_label = {
    s: ("NONE" if not s else "+".join(sorted(s)))
    for s in plans
}

# One bit per budget-1 plan. A future's support mask records exactly which
# admissible plans make that future installable.
support_mask = {}
for q in Gamma:
    mask = 0
    for i, p in enumerate(plans):
        if q in success[p]:
            mask |= (1 << i)
    support_mask[q] = mask

FULL_PLAN_MASK = (1 << len(plans)) - 1

def common_plan_mask(family):
    m = FULL_PLAN_MASK
    for q in family:
        m &= support_mask[q]
    return m

def minimal_obstruction(family):
    if common_plan_mask(family) != 0:
        return False
    n = len(family)
    for k in range(1, n):
        for sub in itertools.combinations(family, k):
            if common_plan_mask(sub) == 0:
                return False
    return True

def private_witness(family, dropped):
    others = tuple(q for q in family if q != dropped)
    m = common_plan_mask(others)
    assert m != 0
    # Since the full family has empty intersection, any plan in m must fail dropped.
    choices = [i for i in range(len(plans)) if (m >> i) & 1]
    for i in choices:
        if not ((support_mask[dropped] >> i) & 1):
            return plans[i]
    raise AssertionError((family, dropped, m, support_mask[dropped]))

obs_by_order = {2: [], 3: [], 4: []}
for k in (2, 3, 4):
    for fam in itertools.combinations(Gamma, k):
        if minimal_obstruction(fam):
            obs_by_order[k].append(fam)

# Strong higher-order checks.
rank3_ok = all(
    all(common_plan_mask(pair) != 0 for pair in itertools.combinations(fam, 2))
    for fam in obs_by_order[3]
)
rank4_ok = all(
    all(common_plan_mask(triple) != 0 for triple in itertools.combinations(fam, 3))
    for fam in obs_by_order[4]
)

print("INSACERMO_POSTCLOSURE_DEBIAN_PLAN_DUALITY_V1")
print("PROTOCOL FROZEN_BEFORE_RESULT")
print("DEBIAN_VERSION", EXPECTED_VERSION)
print("DEBIAN_CODENAME", EXPECTED_CODENAME)
print("RELEASE_SHA256", release_sha256)
print("PACKAGES_SHA256", actual_pkg_sha256)
print("PACKAGES_BYTES", len(packages_xz))
print("PACKAGE_STANZAS", len(stanzas))
print("TARGETS", len(TARGETS), " ".join(TARGETS))
print("CATALOGUE_BUNDLES", len(bundles))
print("BASELINE_FEASIBLE_GAMMA", len(Gamma))
print("PLAN_BUDGET", PLAN_BUDGET)
print("PLAN_COUNT", len(plans))
for i, p in enumerate(plans):
    print("PLAN", i, plan_label[p])
for i, p in enumerate(PERTURB, 1):
    print("STRUCTURAL_PERTURB", i, p, "COVERAGE", len(coverage[p]),
          "TARGETS", ",".join(sorted(coverage[p])))

# Support-pattern census.
patterns = {}
for q in Gamma:
    patterns[support_mask[q]] = patterns.get(support_mask[q], 0) + 1
for mask in sorted(patterns):
    supported = [plan_label[plans[i]] for i in range(len(plans)) if (mask >> i) & 1]
    print("SUPPORT_PATTERN", format(mask, f"0{len(plans)}b"),
          "COUNT", patterns[mask],
          "PLANS", ",".join(supported) if supported else "NONE")

for k in (2, 3, 4):
    print("MINIMAL_OBSTRUCTIONS_ORDER", k, len(obs_by_order[k]))
print("RANK3_PAIRWISE_COMPATIBLE_CHECK", "YES" if rank3_ok else "NO")
print("RANK4_TRIPLEWISE_COMPATIBLE_CHECK", "YES" if rank4_ok else "NO")

all_obs = []
for k in (2, 3, 4):
    all_obs.extend(obs_by_order[k])

for fam in all_obs[:10]:
    print("OBSTRUCTION", "ORDER", len(fam),
          "FUTURES", " | ".join("+".join(q) for q in fam))
    for q in fam:
        p = private_witness(fam, q)
        print("PRIVATE_WITNESS",
              "DROP", "+".join(q),
              "PLAN", plan_label[p],
              "SUPPORTS_OTHERS", "YES",
              "FAILS_DROPPED", "YES")

# Audit every obstruction, not only printed examples.
for fam in all_obs:
    for q in fam:
        p = private_witness(fam, q)
        assert all(other in success[p] for other in fam if other != q)
        assert q not in success[p]

print("ALL_MINIMAL_OBSTRUCTIONS", len(all_obs))
print("PRIVATE_WITNESS_AUDIT", "PASS")
print("RESULT", "COMPLETE")
