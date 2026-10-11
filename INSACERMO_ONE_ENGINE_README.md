# INSACERMO ONE ENGINE — 11 octobre 2026

## Ce qui est effectivement terminé

Une **entrée exécutable unique** `insacermo_one_engine.py` pour la grammaire finie C3 Must/May (croyances entre L et U, ensembles d'actions Must et May, observations, transformations, coûts de probe, dette et réserve strictes) avec une preuve Lean **pour l'instance exacte** avant d'autoriser une action.

Le programme émet ACT, PROBE, REPAIR, REFUSE_ROBUST ou EPISTEMIC_OPEN. Le verdict REFUSE_ROBUST est relatif à la grammaire bornée déclarée ; EPISTEMIC_OPEN est accompagné des deux bornes formelles. PROBE et REPAIR n'autorisent que la **première opération** du plan : il faut attendre l'observation effective et réévaluer l'état avant d'agir sur la branche.

REPAIR doit produire une transformation réelle d'au moins un état atteignable, et cette propriété est vérifiée dans le Lean généré. Une simple étiquette "REPAIR" sur un capteur passif est rejetée.

La vérification Lean échoue fermée : sans Lean, sans fichier compilable, si le contrat est mal formé ou si une preuve falsifiée n'est pas acceptée, aucune action n'est autorisée. L'enveloppe C3, les flags Must/May, les transitions, les capacités et les prix sont présents **dans la même preuve générée**.

## À lancer

Prérequis : Python 3.10+ et Lean 4.33.1 (`elan`). Pas d'API payante, pas de modèle entraîné.

À la racine du dépôt GitHub, compiler le noyau portable **historique inchangé** :

```sh
export LEAN_PATH=.:lean
lean -o C3/PortableFiniteVerifierV1.olean C3/PortableFiniteVerifierV1.lean
lean -o C3/PortableVerifierSoundnessV1.olean C3/PortableVerifierSoundnessV1.lean
lean -o C3/PortableExactSearchV1.olean C3/PortableExactSearchV1.lean
python3 insacermo_one_engine.py examples/one_engine_c3_contract.json sortie_one_engine
python3 insacermo_one_engine.py examples/one_engine_c3_contract.json sortie_one_engine --verify
```

La seconde commande régénère la preuve Lean à partir du contrat, refait la recherche exhaustive du plan déclaré et compare le reçu avant de revérifier Lean. Un hash de reçu **n'est pas** une signature cryptographique ni une preuve de validité du monde physique.

Sur Windows, `LEAN_PATH=.:lean` doit être défini selon le shell utilisé ; les étapes sont exécutées automatiquement par la CI GitHub.

## Liens historiques préservés

- MAX TOTAL historique : théorie et noyaux figés, preuves vérifiées dans leurs runs initiaux.
- V3 : `unified_runtime_v3.py` et tests d'intégration à l'ancien runtime multiprobe.
- C3 dynamique : `experiments/c3_raw_dynamic_autoplan_lean.py`, le générateur d'arbres avec certificats associés.
- C3 Must/May et recherche finie : `C3/DoubleEnvelopeKernel.lean` ; `C3/PortableFiniteVerifierV1.lean`, `C3/PortableVerifierSoundnessV1.lean`, `C3/PortableExactSearchV1.lean`.
- Dette/réserve et futur : `C3/TotalHistoricalMultiProbeIntegrationV1.lean`, `C3/TotalRepairFutureBridgeV1.lean`.
- Source finie désormais unifiée : `insacermo_one_engine.py`.
- Tests et falsifications : `.github/workflows/insacermo-one-engine-e2e.yml`.

## Ce qui n'est pas prouvé

Cette livraison n'est **ni** un moteur universel de découverte des lois physiques, **ni** l'intégration en production de chaque ancien outil/site Netlify. Les vérités du monde, le lien entre données observées et mondes déclarés, la capacité réelle des réparations, et l'exhaustivité hors grammaire restent à établir indépendamment.

Le calcul exhaustif est borné aux dimensions déclarées (8 mondes, 12 actions, 8 sondes, profondeur 4), sous réserve des coûts et du temps d'exécution. Ce n'est pas un solveur industriel de généralisation automatique. Les noyaux Lean historiques ne prouvent pas en bloc l'intégralité du code Python ; ce sont les **certificats de chaque modèle exécuté** qui sont compilés dans la porte de décision.

## Prochaine action seulement si nécessaire

Ne plus recréer les modules, les mêmes exemples ou un nouveau nom de version. Toute continuation se concentre soit sur une faiblesse démontrée par une reproduction indépendante, soit sur l'intégration de cet exécutable à l'application locale existante, sous les mêmes garanties.

## Références

Dépôt : https://github.com/benblak/insacermo-morphology-auto

Branche de livraison : `insacermo-one-engine-c3-complete-finite-20261011`.
