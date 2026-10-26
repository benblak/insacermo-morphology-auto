import blind_scigrid_capacitated_joint_v1 as protocol

# Compatibility correction after run 1 stopped before any MILP result:
# the SciGRID-DE example attaches positive generator capacity records to every
# load bus, so the predeclared "no local generation" eligibility rule yields
# an empty target set. We therefore retain the original fixed ranking variable
# (mean load) and select the top N positive-load buses, without changing any
# scenario, cut ranking, bundle size, repair semantics, or outcome metric.

def top_mean_load_targets(loads, gen_cap):
    return [str(b) for b in loads.index if float(loads.loc[b]) > 1e-9][: protocol.N_TARGETS]


_real_print = print


def transparent_print(*args, **kwargs):
    if len(args) == 1 and args[0] == "TARGET_RULE top_mean_load_buses_without_local_generation":
        return _real_print("TARGET_RULE top_mean_load_buses", **kwargs)
    return _real_print(*args, **kwargs)


protocol.target_buses = top_mean_load_targets
protocol.print = transparent_print

_real_print("COMPATIBILITY_CORRECTION target eligibility only; run 1 produced no MILP outcomes")
protocol.main()
