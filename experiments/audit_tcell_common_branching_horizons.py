import importlib.util
import os

MODULE_PATH = os.path.join(os.path.dirname(__file__), "blind_tcell_common_branching_v2.py")
spec = importlib.util.spec_from_file_location("tcell_v2", MODULE_PATH)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

HORIZONS = (4, 6, 8, 10, 12, 16, 20)
BUNDLES = (
    ("Th0",), ("Th1",), ("Th2",),
    ("Th0", "Th1"), ("Th0", "Th2"), ("Th1", "Th2"),
    ("Th0", "Th1", "Th2"),
)
# Fixed from the blind V2 ranking before this audit; not re-ranked by horizon.
FIXED_SHARED3 = {"SOCS1", "JAK1", "IL4R"}


def fmt(d):
    return "INF" if d >= m.INF else str(d)


def main():
    rules, names = m.parse_bnet(m.MODEL_PATH)
    print("INSACERMO_TCELL_COMMON_BRANCHING_POSTRESULT_HORIZON_AUDIT")
    print("STATUS exploratory/post-result sensitivity analysis; does not modify or replace blind V2")
    print("HORIZONS", ",".join(map(str, HORIZONS)))
    print("FIXED_SHARED3", ",".join(sorted(FIXED_SHARED3)))
    first_finite = {F: None for F in BUNDLES}
    for H in HORIZONS:
        m.PATH_HORIZON = H
        print("HORIZON", H)
        for F in BUNDLES:
            d = m.recovery_depth(rules, names, F, set(), set())
            if d < m.INF and first_finite[F] is None:
                first_finite[F] = H
            print("BASELINE", ",".join(F), fmt(d))
        for F in (("Th1", "Th2"), ("Th0", "Th1", "Th2")):
            d = m.recovery_depth(rules, names, F, FIXED_SHARED3, set())
            print("SHARED3", ",".join(F), fmt(d))
    print("FIRST_TESTED_FINITE_HORIZON")
    for F in BUNDLES:
        h = first_finite[F]
        print(",".join(F), "NONE_UP_TO_20" if h is None else h)
    print("INTERPRETATION none-up-to-20 is still a bounded negative result, not a proof of infinite-horizon irreversibility")


if __name__ == "__main__":
    main()
