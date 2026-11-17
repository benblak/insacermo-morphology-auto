# INSACERMO — CONTRE-TEST MÉMOIRE / FUTURS / GARANTIES (17 NOV. 2026)

**Audit local reproductible. NOUVEAU RÉSULTAT NÉGATIF.** Noyau historique MAX TOTAL/C3, site et versions gelées inchangés. Ce run n'est **PAS** une compilation Lean.

## Hypothèse pré-définie

Un proxy causal de la contraction mémoire/cohérence prédit-il mieux qu'une règle simple les violations futures d'un seuil, dans **deux** séries physiques d'archives, sans ajustement sur la période finale ?

Critère à satisfaire sur CHAQUE série : AUROC >=0.65 et >= meilleur des trois comparateurs (niveau courant, pente, volatilité). Seuil = 80e percentile de la partie entraînement 60%. Segment intermédiaire 20% ignoré ; évaluation finale 20%. Fenêtres 24 mois / 22 années ; horizons 6 mois / 3 ans ; signal construit exclusivement à partir du passé, mais **ce n'est pas la métrique historique INSACERMO-U TCI/Xi**.

SHA256 du protocole local figé avant premier calcul : `8cff7990396f0e48881c66eaec14274ffd113dfee740ec5562ac338893888b5c`. Ce préenregistrement local ne constitue pas un scellement public cryptographique antérieur aux données historiques. Une erreur de dimension du comparateur saisonnier a été corrigée avant le premier résultat calculé.

## Résultats locaux exécutés et contre-vérifiés

| Données historiques statsmodels | Intervalles testés | Violations futures | AUC indicateur candidat | Baseline simple la plus forte | Résultat |
|---|---:|---:|---:|---:|---|
| El Niño / températures mensuelles équatoriales | 141 | 92 | 0.562999 | volatilité 0.535714 | **FAIL** (<0.65) |
| Taches solaires annuelles | 59 | 36 | 0.552536 | pente 0.782609 | **FAIL** (deux critères) |

**VERDICT EMPIRIQUE : REFUSE_GENERAL_EMPIRICAL_LINK.** Cela ne prouve pas l'absence de tout lien physique ; cela réfute la revendication empirique générale dans les conditions pré-déclarées et avec cet indicateur simplifié.

Le recalcul de toutes les étiquettes, 200 scores de prédiction, AUROC et baselines via un auditeur Python séparé a donné **INDEPENDENT_BRIDGE_AUDIT_PASS_AND_GENERAL_EMPIRICAL_CLAIM_REFUSED**. Receipt local SHA256 (fichier results.json) : `1e72bdf8aa6198598c3dcbb474431727fe9560aa5f1e47464a58613d2e1d09bb`.

## Contrôles mathématiques finis séparés

1. Même score de contraction directionnelle 2/3, même début/fin, mais maxima 3 et 4. Un contrat de seuil 3.5 distingue les histoires : le score seul n'est pas un état décisionnel universel.
2. Réduction du belief `B' ⊆ B` à capacités constantes ne supprime aucune action déjà sûre, preuve d'inclusion et vérification des 8 sous-ensembles du cas à trois mondes.
3. Obstruction d'ordre trois : chaque paire de mondes a une action commune mais le triplet n'en a aucune. Une PROBE distinguant le cas ou une REPAIR ajoutant une action universelle restaure l'actionnabilité selon le contrat.
4. Une suite infinie de politiques `π_n` valables jusqu'à horizon `n` ne donne pas nécessairement une même politique valable pour l'horizon infini.

**Interprétation :** contraction des hypothèses épistémiques ≠ contraction des futurs physiques ≠ perte des actions garanties. Le lien entre mesures mémorielles historiques et garantie C3 reste ouvert. Cette distinction ne remplace ni les théorèmes C3, ni l'ancien moteur, ni les preuves XOR du 17 novembre.

Archive autonome fournie à l'utilisateur : `INSACERMO_BRIDGE_MEMOIRE_FUTURS_TEST_20261117.zip` contenant PREREG.md, run.py, independent_audit.py, results.json, independent_receipt.json, REPORT_FR.md et SHA256SUMS.txt. Cet archivage GitHub textuel a été effectué **après** l'exécution, et ne doit pas être décrit comme un pré-enregistrement GitHub.
