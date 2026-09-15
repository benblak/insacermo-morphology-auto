# INSACERMO Obstruction Depth Benchmark V0.1

This benchmark is the empirical companion to the finite obstruction-rank / local-audit kernel.
It applies one fixed contract to three real network datasets shipped with NetworkX:

- Zachary Karate Club
- Florentine Families
- Davis Southern Women

## Contract

For every selected undirected edge `{u,v}`, require

```text
x_u != x_v
```

An inclusion-minimal unsatisfiable edge subcontract is exactly a simple odd cycle.
Therefore:

- detection depth = length of the shortest odd cycle;
- certification depth = length of the longest simple odd cycle;
- the odd-cycle length distribution is the obstruction-depth profile.

Each maximal odd-cycle witness is also translated to 2-CNF. An edge `{u,v}` becomes

```text
(x_u OR x_v) AND (!x_u OR !x_v)
```

The benchmark verifies the resulting CNF with an exact implication-graph / strongly-connected-components 2-SAT check. It also deletes each clause once and confirms that every single-clause deletion is satisfiable, establishing the witness as a MUS.

## Reproduce

```bash
python -m pip install -r requirements.txt
python benchmark.py --out results --check
```

Expected headline results:

| dataset | nodes | edges | detection depth | certification depth | odd-cycle obstructions | max witness CNF |
|---|---:|---:|---:|---:|---:|---:|
| Zachary Karate | 34 | 78 | 3 | 19 | 365521 | 38-clause MUS |
| Florentine Families | 15 | 20 | 3 | 9 | 20 | 18-clause MUS |
| Davis Southern Women | 32 | 89 | none | none | 0 | none |

The Davis graph is bipartite and serves as a negative control.

## Canonical dataset hashes

The benchmark serializes each undirected edge once as a lexicographically sorted `u,v` row and hashes that canonical edge text with SHA-256.

- Zachary Karate: `63fd5c5b1770d295c23d76e096a6672f4e695205a95b23ea0039fa519375223f`
- Florentine Families: `f6fdd3ea273f8be98217089e149f18deb0b4277857666c4df5bc86c928662805`
- Davis Southern Women: `43ac43dd4435203d0219dabf52813f991ea29123b636f4066dda3222b28a9a98`

## Status

This directory is an **EMPIRICAL ANCHOR + MECHANICAL AUDIT**. The abstract obstruction-rank / local-audit equivalence and its Signed XOR, Hypergraph Actionability and CNF/MUS bridges are verified separately in Lean.
