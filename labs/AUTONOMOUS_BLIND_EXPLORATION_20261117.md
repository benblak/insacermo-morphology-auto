# INSACERMO — autonomous blind search (isolated exploratory lab, 2026-11-17)

Checkpoint: third-domain transfer **failed on efficiency**, while stopping decisions remained exact.

- Third-domain data: 19,735 appliance-energy rows; 2,434 8-reading groups.
- Selected: 9,937 queries; exact random expectation: 9,905.1214.
- Net after 256 calibration queries: **−287.8786 queries saved**, i.e. a loss; 0 contradicted decisions.
- Original historical C3/Lean artifacts remain frozen. Do NOT tune this evaluation after observing its outcome.
- See branch `lab/c3-third-domain-appliances-preregistered-20261117`, report `labs/third_domain_results_20261117/audit.json`.

Next scientific goal: autonomous discovery without candidate formula list.
Exploratory local Python test created five hidden **synthetic Boolean rules**;
the synthesizer grew 21,075 behavior classes from a declared basic grammar
(five binary bits; constants and AND/OR/XOR; max expression cost nine),
chose challenge measurements via maximal candidate disagreement,
revised provisional rules upon contradictions, and either reconstructed an
exact finite truth table or refused the specified representation class.

First local run: four full-domain reconstructions (32/32 queries each),
one model-class refusal after 16 queries. Three further randomized local
runs produced the same *pattern*, with variable exact counts.
Local run is **not** a new GitHub Actions SUCCESS, and it has **no new
Lean proof**. It demonstrates restricted autonomous hypothesis generation
and adaptive testing, not general discovery of a physical law.

No new historical INSACERMO engine version or kernel change is authorized.

Reference source scripts and complete local audits are delivered separately
as a reproducible ZIP in the conversation, not yet stored in this branch.
