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
BUDGET = 1

ROOT = Path("debian_insacermo_work")
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

assert field_value("Version") == EXPECTED_VERSION, (field_value("Version"), EXPECTED_VERSION)
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
assert actual_pkg_sha256 == expected_pkg_sha256, (actual_pkg_sha256, expected_pkg_sha256)
assert len(packages_xz) == expected_pkg_size, (len(packages_xz), expected_pkg_size)
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
by_name = {}
for fields, raw in stanzas:
    by_name[fields["Package"]] = (fields, raw)

for target in TARGETS:
    assert target in by_name, f"target absent from Debian main amd64: {target}"

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
    seen = set()
    stack = [start]
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
    # Avoid universal dependencies and target-specific leaves: the perturbation
    # classes must affect multiple but not all fixed target futures.
    return 2 <= k < len(TARGETS)

candidates = [p for p in coverage if structurally_eligible(p)]
assert len(candidates) >= 3, len(candidates)

# Frozen outcome-independent structural selection:
# c1 maximizes target-cone coverage; c2 maximizes Hamming diversity from c1;
# c3 maximizes its minimum Hamming diversity from both c1 and c2.
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
    parts = []
    for fields, raw in stanzas:
        if fields["Package"] not in removed:
            parts.append(raw.rstrip() + "\n")
    for bundle in bundles:
        name = contract_name[bundle]
        parts.append(
            f"Package: {name}\n"
            f"Version: 1\n"
            f"Architecture: amd64\n"
            f"Depends: {', '.join(bundle)}\n"
            f"Description: INSACERMO synthetic future contract {'+'.join(bundle)}\n"
        )
    path = ROOT / ("repo_" + ("none" if not restored else "_".join(sorted(restored))) + ".Packages")
    path.write_text("\n".join(parts) + "\n", encoding="utf-8")
    return path

def exact_success_set(restored):
    repo = repo_for(restored)
    requested = ",".join(contract_name[b] for b in bundles)
    cmd = [
        "dose-debcheck",
        "--quiet",
        "--deb-native-arch=amd64",
        "--failures",
        "--checkonly", requested,
        str(repo),
    ]
    p = subprocess.run(cmd, text=True, capture_output=True, timeout=240)
    if p.returncode not in (0, 1):
        raise RuntimeError(
            f"dose-debcheck abnormal exit {p.returncode}\nSTDOUT:\n{p.stdout}\nSTDERR:\n{p.stderr}"
        )
    failed = set(
        re.findall(r"(?mi)^package:\s*(insacermo-contract-\d+)\s*$", p.stdout)
    )
    unknown = failed - set(bundle_of)
    assert not unknown, unknown
    return {b for b in bundles if contract_name[b] not in failed}

all_subsets = []
for r in range(0, len(PERTURB) + 1):
    for subset in itertools.combinations(PERTURB, r):
        all_subsets.append(frozenset(subset))

success = {}
for subset in all_subsets:
    success[subset] = exact_success_set(subset)

full = frozenset(PERTURB)
baseline = success[full]

# Sanity: all fixed singleton target futures must be installable in intact
# Debian stable main; otherwise the fixed target catalogue is invalid.
for t in TARGETS:
    assert (t,) in baseline, t

Gamma = sorted(baseline, key=lambda b: (len(b), b))
assert Gamma, "empty baseline-feasible future family"

def minimal_obstructions(success_set):
    obs = []
    for b in bundles:
        if b in success_set or len(b) == 1:
            continue
        proper_ok = True
        for r in range(1, len(b)):
            for sub in itertools.combinations(b, r):
                if sub not in success_set:
                    proper_ok = False
                    break
            if not proper_ok:
                break
        if proper_ok:
            obs.append(b)
    return obs

repair_price = {}
for b in Gamma:
    feasible_subsets = [s for s in all_subsets if b in success[s]]
    assert feasible_subsets, b
    repair_price[b] = min(len(s) for s in feasible_subsets)

hist = {k: 0 for k in range(4)}
for v in repair_price.values():
    hist[v] += 1

one_actions = [frozenset([p]) for p in PERTURB]
action_stats = []
for a in one_actions:
    now = sum(b in success[a] for b in Gamma)
    residual_prices = []
    for b in Gamma:
        # Additional classes needed after the already-restored class a.
        options = [
            len(s - a)
            for s in all_subsets
            if a.issubset(s) and b in success[s]
        ]
        residual_prices.append(min(options))
    action_stats.append((
        next(iter(a)),
        now,
        len(Gamma) - now,
        sum(residual_prices) / len(residual_prices),
        max(residual_prices),
    ))

best = min(action_stats, key=lambda x: (x[2], x[3], x[0]))

print("INSACERMO_POSTFREEZE_DEBIAN_INSTALLABILITY_V1")
print("STATUS BLIND_POSTFREEZE_EXTERNAL_VALIDATION")
print("DEBIAN_VERSION", EXPECTED_VERSION)
print("DEBIAN_CODENAME", EXPECTED_CODENAME)
print("RELEASE_SHA256", release_sha256)
print("PACKAGES_SHA256", actual_pkg_sha256)
print("PACKAGES_BYTES", len(packages_xz))
print("PACKAGE_STANZAS", len(stanzas))
print("TARGETS", len(TARGETS), " ".join(TARGETS))
print("CATALOGUE_BUNDLES", len(bundles))
print("BASELINE_FEASIBLE_GAMMA", len(Gamma))
print("MAX_BUNDLE", MAX_BUNDLE)
print("BUDGET", BUDGET)
print("SOLVER DOSE_DEBCHECK_EXACT_METADATA_INSTALLABILITY")
print("SEMANTICS Debian metadata co-installability under Depends/Pre-Depends/Conflicts/Breaks/Provides; repair cost is restored package-class count")
for i, p in enumerate(PERTURB, 1):
    print(
        "STRUCTURAL_PERTURB", i, p,
        "COVERAGE", len(coverage[p]),
        "TARGETS", ",".join(sorted(coverage[p]))
    )

for subset in sorted(all_subsets, key=lambda s: (len(s), tuple(sorted(s)))):
    label = "NONE" if not subset else "+".join(sorted(subset))
    safe = sum(b in success[subset] for b in Gamma)
    obs = minimal_obstructions(success[subset])
    print(
        "RESTORED", label,
        "COST", len(subset),
        "SAFE", safe,
        "FAILED", len(Gamma) - safe,
        "SURVIVAL_MASS", f"{safe/len(Gamma):.12f}",
        "MINIMAL_OBSTRUCTIONS", len(obs),
        "MIN_OBS_SIZE2", sum(len(b) == 2 for b in obs),
        "MIN_OBS_SIZE3", sum(len(b) == 3 for b in obs),
    )

print(
    "REPAIR_PRICE_HIST",
    " ".join(f"C{k}:{hist[k]}" for k in sorted(hist))
)
for name, now, failed, mean_resid, max_resid in action_stats:
    print(
        "ACTION", name,
        "COST 1",
        "SAFE_NOW", now,
        "FAILED_NOW", failed,
        "FAILURE_RISK", f"{failed/len(Gamma):.12f}",
        "MEAN_RESIDUAL_REPAIR_PRICE", f"{mean_resid:.12f}",
        "MAX_RESIDUAL_REPAIR_PRICE", max_resid,
    )
print("BUDGET1_DECISION_MIN_FAILURE_RISK", best[0])
print("RESULT COMPLETE")
