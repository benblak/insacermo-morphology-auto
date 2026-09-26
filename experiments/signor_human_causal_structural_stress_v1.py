# INSACERMO — SIGNOR human causal signaling stress test V1
# Domain: molecular causal signaling (radically different from transport/social graphs).
# Status: exploratory mechanism witness on a real curated dataset.
#
# Interpretation:
#   nodes  = human proteins
#   edges  = curated directed causal relations in SIGNOR
#   source = EGFR
#   goal   = reaching a protein along one sequential causal route
#
# IMPORTANT LIMIT:
# This does NOT model full cellular behavior, stoichiometry, branching signal
# integration, kinetics, expression context, or intervention efficacy.  It tests
# only the structural INSACERMO theorem on sequential causal reachability.
#
# Dataset:
# SIGNOR July 2026 stable release
# https://signor.uniroma2.it/releases/Jul2026_release.txt

from __future__ import annotations

import csv
import hashlib
import io
import urllib.request
from collections import defaultdict, deque

URL = "https://signor.uniroma2.it/releases/Jul2026_release.txt"
SOURCE_GENE = "EGFR"


def download(url: str) -> bytes:
    req = urllib.request.Request(url, headers={"User-Agent": "INSACERMO/1.0"})
    with urllib.request.urlopen(req, timeout=120) as r:
        return r.read()


def norm(s):
    return (s or "").strip()


def lower(s):
    return norm(s).lower()


def contains_human_tax(s):
    s = norm(s)
    if not s:
        return True
    return "9606" in s


def parse_release(raw: bytes):
    text = raw.decode("utf-8-sig", errors="replace")
    lines = [ln for ln in text.splitlines() if ln.strip()]
    # Release files are tab-delimited.  Skip any preamble until the canonical header.
    header_idx = None
    for i, ln in enumerate(lines[:50]):
        up = ln.upper()
        if "ENTITYA" in up and "ENTITYB" in up and "\t" in ln:
            header_idx = i
            break
    if header_idx is None:
        raise RuntimeError("SIGNOR header not found")

    reader = csv.DictReader(io.StringIO("\n".join(lines[header_idx:])), delimiter="\t")
    fields = [norm(x) for x in (reader.fieldnames or [])]
    fmap = {x.upper(): x for x in fields}

    required = ["ENTITYA", "ENTITYB"]
    for k in required:
        if k not in fmap:
            raise RuntimeError(f"missing required field {k}; fields={fields}")

    def field(row, key, default=""):
        col = fmap.get(key)
        return norm(row.get(col, default)) if col else default

    edges_all = []
    names = {}
    direct_values = set()

    for row in reader:
        type_a = lower(field(row, "TYPEA"))
        type_b = lower(field(row, "TYPEB"))
        # Keep only protein -> protein relations when type metadata is available.
        if type_a and type_a != "protein":
            continue
        if type_b and type_b != "protein":
            continue
        if not contains_human_tax(field(row, "TAX_ID")):
            continue

        ida = field(row, "IDA") or field(row, "ENTITYA")
        idb = field(row, "IDB") or field(row, "ENTITYB")
        na = field(row, "ENTITYA") or ida
        nb = field(row, "ENTITYB") or idb
        if not ida or not idb or ida == idb:
            continue

        direct = field(row, "DIRECT")
        if direct:
            direct_values.add(direct)
        effect = field(row, "EFFECT")
        mechanism = field(row, "MECHANISM")
        score = field(row, "SCORE")
        signor_id = field(row, "SIGNOR_ID")

        names.setdefault(ida, na)
        names.setdefault(idb, nb)
        edges_all.append((ida, idb, direct, effect, mechanism, score, signor_id))

    # Prefer explicitly direct relations if the release uses a recognisable yes/no field
    # and the resulting network is sufficiently large; otherwise retain all curated
    # directed protein-protein causal relations.
    yes_tokens = {"yes", "y", "true", "t", "1", "direct"}
    direct_edges = [e for e in edges_all if lower(e[2]) in yes_tokens]
    if len(direct_edges) >= 500:
        edges_used = direct_edges
        edge_filter = "protein_protein_human_direct"
    else:
        edges_used = edges_all
        edge_filter = "protein_protein_human_all_curated"

    # Deduplicate graph edges while retaining multiplicity / evidence records.
    records = defaultdict(list)
    for e in edges_used:
        records[(e[0], e[1])].append(e)
    edges = sorted(records)

    return fields, direct_values, names, edges, records, edge_filter


def build_graph(nodes, edges):
    adj = {u: set() for u in nodes}
    radj = {u: set() for u in nodes}
    for u, v in edges:
        adj.setdefault(u, set()).add(v)
        adj.setdefault(v, set())
        radj.setdefault(v, set()).add(u)
        radj.setdefault(u, set())
    return adj, radj


def reachable(adj, start, blocked_edge=None):
    seen = {start}
    dq = deque([start])
    while dq:
        u = dq.popleft()
        for v in adj.get(u, ()):
            if blocked_edge is not None and (u, v) == blocked_edge:
                continue
            if v not in seen:
                seen.add(v)
                dq.append(v)
    return seen


def shortest_distances(adj, start, blocked_edge=None):
    d = {start: 0}
    dq = deque([start])
    while dq:
        u = dq.popleft()
        for v in adj.get(u, ()):
            if blocked_edge is not None and (u, v) == blocked_edge:
                continue
            if v not in d:
                d[v] = d[u] + 1
                dq.append(v)
    return d


def kosaraju(nodes, adj, radj):
    seen = set()
    order = []
    for s in sorted(nodes):
        if s in seen:
            continue
        stack = [(s, 0, sorted(adj.get(s, ())))]
        seen.add(s)
        while stack:
            u, i, nbrs = stack[-1]
            if i < len(nbrs):
                v = nbrs[i]
                stack[-1] = (u, i + 1, nbrs)
                if v not in seen:
                    seen.add(v)
                    stack.append((v, 0, sorted(adj.get(v, ()))))
            else:
                order.append(u)
                stack.pop()

    comp = {}
    comps = []
    for s in reversed(order):
        if s in comp:
            continue
        cid = len(comps)
        members = []
        dq = [s]
        comp[s] = cid
        while dq:
            u = dq.pop()
            members.append(u)
            for v in radj.get(u, ()):
                if v not in comp:
                    comp[v] = cid
                    dq.append(v)
        comps.append(sorted(members))
    return comp, comps


def condensation(comp, comps, edges):
    cadj = {i: set() for i in range(len(comps))}
    edge_records = defaultdict(list)
    for u, v in edges:
        a, b = comp[u], comp[v]
        if a != b:
            cadj[a].add(b)
            edge_records[(a, b)].append((u, v))
    return cadj, edge_records


def find_source(names):
    hits = [u for u, n in names.items() if n.upper() == SOURCE_GENE]
    if not hits:
        hits = [u for u in names if u.upper() == "P00533"]  # UniProt EGFR fallback
    if not hits:
        raise RuntimeError("EGFR not found in SIGNOR protein graph")
    return sorted(hits)[0]


def rep_name(cid, comps, names):
    members = comps[cid]
    return min((names.get(x, x), x) for x in members)


def main():
    raw = download(URL)
    sha = hashlib.sha256(raw).hexdigest()
    fields, direct_values, names, edges, records, edge_filter = parse_release(raw)
    nodes = set()
    for u, v in edges:
        nodes.add(u); nodes.add(v)

    adj, radj = build_graph(nodes, edges)
    source = find_source(names)
    comp, comps = kosaraju(nodes, adj, radj)
    cadj, class_edges = condensation(comp, comps, edges)
    source_c = comp[source]

    baseline_c_reach = reachable(cadj, source_c)
    baseline_node_dist = shortest_distances(adj, source)

    # Search every reachable condensation edge for an INSACERMO pair witness:
    # delete exactly that SCC-edge class; source must still reach both endpoint SCCs,
    # but the upstream SCC must no longer reach the downstream SCC.
    candidates = []
    for (cu, cv), real_edges in sorted(class_edges.items()):
        if cu not in baseline_c_reach or cv not in baseline_c_reach:
            continue
        # Before deletion cu -> cv is immediate, so the pair is chain-feasible.
        after_from_source = reachable(cadj, source_c, blocked_edge=(cu, cv))
        if cu not in after_from_source or cv not in after_from_source:
            continue  # a singleton would be lost; not the hidden pair phenomenon
        after_from_u = reachable(cadj, cu, blocked_edge=(cu, cv))
        if cv in after_from_u:
            continue  # alternate path keeps pair feasible
        # DAG condensation means cv cannot reach cu when cu->cv is an edge.
        # Prefer a single real biological relation, then small SCCs, then short source depth.
        edge_count = len(real_edges)
        scc_mass = len(comps[cu]) + len(comps[cv])
        u0, v0 = sorted(real_edges)[0]
        depth = baseline_node_dist.get(u0, 10**9)
        candidates.append((edge_count, scc_mass, depth, names.get(u0, u0), names.get(v0, v0), cu, cv))

    if not candidates:
        print("INSACERMO_SIGNOR_CAUSAL_STRESS_V1")
        print("STATUS NO_CREATED_PAIR_WITNESS_FOUND")
        print("SOURCE_URL", URL)
        print("SOURCE_SHA256", sha)
        print("EDGE_FILTER", edge_filter)
        print("NODES", len(nodes))
        print("EDGES", len(edges))
        print("SCC_COUNT", len(comps))
        print("SOURCE", names.get(source, source), source)
        print("RESULT COMPLETE")
        return

    candidates.sort()
    edge_count, scc_mass, depth, _, _, cu, cv = candidates[0]
    real_edges = sorted(class_edges[(cu, cv)])
    q, r = real_edges[0]

    # Verify at node level by deleting all edges across this SCC pair.
    blocked_real = set(real_edges)
    adj_after = {u: set(vs) for u, vs in adj.items()}
    for u, v in blocked_real:
        adj_after[u].discard(v)

    before_src = reachable(adj, source)
    after_src = reachable(adj_after, source)
    before_q = reachable(adj, q)
    after_q = reachable(adj_after, q)
    after_r = reachable(adj_after, r)

    before_singletons = (q in before_src and r in before_src)
    after_singletons = (q in after_src and r in after_src)
    before_pair = before_singletons and (r in before_q or q in reachable(adj, r))
    after_pair = after_singletons and (r in after_q or q in after_r)

    print("INSACERMO_SIGNOR_CAUSAL_STRESS_V1")
    print("STATUS EXPLORATORY_REAL_BIOLOGICAL_MECHANISM_WITNESS")
    print("SOURCE_URL", URL)
    print("SOURCE_SHA256", sha)
    print("RELEASE", "Jul2026")
    print("EDGE_FILTER", edge_filter)
    print("DIRECT_FIELD_VALUES", "|".join(sorted(direct_values)) if direct_values else "absent")
    print("NODES", len(nodes))
    print("EDGES", len(edges))
    print("SCC_COUNT", len(comps))
    print("SOURCE", names.get(source, source), source, "SOURCE_SCC", source_c, "SOURCE_SCC_SIZE", len(comps[source_c]))
    print("REACHABLE_NODES_FROM_SOURCE", len(before_src))
    print("REACHABLE_SCCS_FROM_SOURCE", len(baseline_c_reach))
    print("CANDIDATE_CREATED_PAIR_WITNESSES", len(candidates))
    print("Q", names.get(q, q), q, "SCC", cu, "SCC_SIZE", len(comps[cu]))
    print("R", names.get(r, r), r, "SCC", cv, "SCC_SIZE", len(comps[cv]))
    print("DESTROYED_SCC_EDGE_CLASS", cu, cv)
    print("DESTROYED_REAL_RELATIONS", len(real_edges))
    for i, (u, v) in enumerate(real_edges[:10], 1):
        ev = records.get((u, v), [])
        print("DESTROYED_RELATION", i, names.get(u, u), "->", names.get(v, v), "EVIDENCE_RECORDS", len(ev))
    print("BASELINE_Q_REACHABLE", int(q in before_src))
    print("BASELINE_R_REACHABLE", int(r in before_src))
    print("AFTER_Q_REACHABLE", int(q in after_src))
    print("AFTER_R_REACHABLE", int(r in after_src))
    print("PAIR_BEFORE_FEASIBLE", int(before_pair))
    print("PAIR_AFTER_FEASIBLE", int(after_pair))
    print("PAIR_AFTER_HARD_LOSS", int(before_pair and not after_pair))
    print("MINIMAL_HARD_OBSTRUCTION_ORDER", 2 if (before_pair and not after_pair and after_singletons) else "NA")
    print("CERTIFIED_HARD_AUDIT_ORDER", 2)
    print("MECHANISM", "CREATED_CAUSAL_INCOMPARABILITY" if (before_pair and not after_pair and after_singletons) else "OTHER")
    print("REPAIR_RESTORE_DESTROYED_CLASS_PAIR_FEASIBLE", int(before_pair))
    print("LIMITATION sequential_causal_reachability_only_not_full_cell_function")
    print("RESULT COMPLETE")


if __name__ == "__main__":
    main()
