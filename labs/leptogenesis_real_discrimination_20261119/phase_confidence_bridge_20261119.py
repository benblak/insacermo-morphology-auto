"""Lab continuation: 2018/2021 published phase ranges vs 2026 detector projections.
STRICTLY an illustrative Gaussian proxy, NOT detector data or new Lean proof.
The historical C3 engine and previously validated Lean files are unchanged.
"""
from collections import Counter
from statistics import NormalDist

A = range(198, 226)
B = tuple(range(5, 41)) + tuple(range(320, 356))
CASES = (("DUNE2026_300_95", 27, .95), ("DUNE2026_600_95", 22, .95),
         ("DUNE2026_600_99", 22, .99), ("DUNE2026_1000_99", 18, .99),
         ("HyperK2026_95", 20, .95), ("HyperK2026_99", 20, .99))


def distance(a, b):
    d = abs(a - b) % 360
    return min(d, 360 - d)


def classify(center, radius):
    a = any(distance(center, phase) <= radius for phase in A)
    b = any(distance(center, phase) <= radius for phase in B)
    return "BOTH" if a and b else "A_ONLY" if a else "B_ONLY" if b else "NEITHER"


def main():
    assert min(distance(a, b) for a in A for b in B) == 95
    assert classify(272, 47) == "A_ONLY"
    assert classify(272, 48) == "BOTH"
    for label, sigma, level in CASES:
        radius = sigma * NormalDist().inv_cdf((1 + level) / 2)
        counts = Counter(classify(z, radius) for z in range(360))
        print(label, "halfwidth_deg", round(radius, 3), "centers", dict(counts))
        if label in ("DUNE2026_600_95", "DUNE2026_1000_99", "HyperK2026_95"):
            assert counts["BOTH"] == 0
        else:
            assert counts["BOTH"] > 0
    print("CONDITIONAL_GAUSSIAN_PROXY_TESTS_SUCCESS")


if __name__ == "__main__":
    main()
