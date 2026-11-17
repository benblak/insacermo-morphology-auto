# INSACERMO — Core breakthrough lab: self-constructed Boolean quotient, then counterexample-driven repair
2026-11-17. **No historical MAX TOTAL / C3 / Lean modification.** Pre-registration: `labs/SELF_CONSTRUCTED_QUOTIENT_PREREG_20261117.md` committed `fdcf36f7407a9e37f45018cd1e61d72fb7ab2d64`. Independent adversarial repair protocol separately committed **before** its run as `labs/QUOTIENT_REPAIR_STRESS_PREREG_20261117.md` at `0409548384f896f35c3382c99c2d18f108b2e8d9`.

## Empirical discovery (not a claim to invent mathematics ex nihilo)
24-bit oracle, 16,777,216 possible inputs. The learner is not given target equation, relevant feature set, monotonicity premise, or a list of candidate law families. It is **given** a general Boolean Shannon IF-THEN-ELSE grammar, which it uses to create reduced shared decision DAGs from actively queried values.

| case | inferred effective variables | oracle queries | DAG internal nodes | final |
|---|---:|---:|---:|---|
| Mixed composition | 7 | 2726 | 13 | exact projected truth |
| Nested conditional | 8 | 2809 | 19 | exact projected truth |
| Parity/gate mix | 7 | 2714 | 14 | exact projected truth |
| Threshold composition | 9 | 3106 | 35 | exact projected truth |
| Clean reference composition | 7 | 2681 | 9 | exact projected truth |
| Same reference with one precommitted unseen flipped input | 7 observed (true global influence = 24) | 2681 | 9 | same model/transcript as clean; correctly REFUSE_UNCONDITIONAL |

Independent post-seal auditor: **PASS; 5/5 clean cases recovered the relevant support and the complete projected table; fresh random 1,024/1,024 per case.** Clean and rare-needle case had identical 2,681-query indices, answer hashes and synthesized graph despite different full-domain law.

## Explicit repair experiment — the missing ability under controlled distribution shift
Two controls unavailable during 100 discovery intervention contexts, then become available. A fixed synthetic hidden law has a conditional AND interaction involving these two controls and one previously active input. On the **9th challenge**, a new observation contradicts the first synthesized graph. The program autonomously tests 24 one-bit interventions, finds both new relevant bits **15 and 21**, expands inferred support from **7 to 9**, and synthesizes a NEW decision DAG.

Independent replay checks all 192 challenge observations and their predictions; complete 512-point projected table exactly matches held-out generator; 2,048/2,048 independent random full-input checks correct. Separate post-seal audit: **PASS**. Total 2,918 unique oracle queries. One contradiction and one graph repair, no human intermediate choice. The control restriction/stage transition is **designer-imposed**, so this is a controlled ability demonstration, not proof of general autonomous structure invention.

## Vital limitations
No physical law novelty, no exhaustive identification of unrestricted 24-bit law, no universal optimality of query order, no cryptographic secrecy, no new Lean proof of the learner. All verdicts **REFUSE_UNCONDITIONAL**; the unseen-needle impossibility is demonstrated, not resolved. Original Lean proof on possibility of indistinguishable unqueried completions remains valid. Python audit is separate code, but both programs share a deterministic synthetic oracle generator after the search is sealed. The 3-law metagrammar from the prior experiment is NOT used; universal Boolean Shannon primitive is still programmed. No historical kernel modification.

## Complete reproducible artifact
Conversation package `INSACERMO_CORE_SELF_CONSTRUCTED_LAW_REPAIR_20261117.zip`, SHA256 `cbdfa69bbeac3612908d09d24fefa623e193984ce5e0ceeef49aa18fdec3193e`, includes six-case transcripts and graphs, the separate repair experiment, two independent auditors, source, and source digests. Runs using only Python standard library. No new external dependencies.
