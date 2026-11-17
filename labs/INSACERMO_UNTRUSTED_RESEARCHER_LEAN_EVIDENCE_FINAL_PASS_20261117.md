# INSACERMO — certificat fondé sur les observations : PASS Lean 4.33.1 (17 novembre 2026)

## Résultat vérifié directement sur GitHub Actions

- Run GitHub Actions **44161578622**, conclusion **success** (commit initial `3d4d803b29d5dd9a2584d829b7a2928feba2a354`).
- Workflow : `.github/workflows/insacermo-untrusted-python-trace-proof.yml`.
- Cause des deux échecs précédents : Lean installé par `elan`, mais son répertoire absent du `PATH` lors de l'étape immédiatement suivante. Journaux run 44150298420 et 44155329937 : `lean: command not found`, code 127. Correction explicite `echo "$HOME/.elan/bin" >> "$GITHUB_PATH"` et appel direct `"$HOME/.elan/bin/lean" --version`.
- Troisième essai run 44161383061 : Lean compilateur installé et actif ; 2107 contrôles source réussis, mais `bv_decide` échouait parce que les noms des deux formules restaient opaques. Correction `unfold <nom>_quadratic <nom>_transported` avant `bv_decide`.
- **Run 44161578622 : succès de toutes les étapes**.
- Preuves générées à partir du transcript scellé (SHA256 `92ef984d87640c1dd107318c1ba51b55fbe21f07e0f3a36ea548eebf5d50876d`). Fichier Lean SHA256 `99b1204f8a93cd3879ba0b98c737206732fbfadf80f351402ff8bbc8364db99b`.
- **2107 théorèmes Lean** validant les réponses **déclarées** aux 301 entrées élémentaires de chacun des sept modèles quadratiques ; indépendamment, les 5309 réponses de l'oracle ont été rejouées et auditables avec `INDEPENDENT_XOR_UNIFIED_PASS`.
- **7 théorèmes Lean pour toutes les entrées BitVec 24** établissent identité entre représentation transportée XOR et ANF quadratique correspondante, conditionnellement aux modèles déclarés.
- Théorème générique Lean : une exception sur une entrée non observée est indiscernable sur le transcript.
- **Attaque 1** : falsifier l'observation `source_0` au point zéro → `lean_mutated_label_exit=1` ; Lean dit explicitement que la proposition `source_0_quadratic 0#24 = false` est fausse.
- **Attaque 2** : corrompre un masque XOR → `lean_mutated_coordinate_exit=1` ; Lean donne un contre-exemple explicite `x = 370699#24`.
- Original `insacermo_one_engine.py` reste inchangé (Git blob SHA1 `bd5310b3692bcbad4e874005b7dd8eda90616f74`).
- Aucune preuve de correction universelle du chercheur Python, aucune preuve qu'un oracle réel arbitraire est quadratique ; le cas à exception synthétique `target_rare` est un contre-exemple à une conclusion globale, et le modèle scellé déclare `REFUSE_UNCONDITIONAL`.

## Justificatifs

- Run : https://github.com/benblak/insacermo-morphology-auto/actions/runs/44161578622
- `labs/untrusted_trace_results_20261117/final_audit.json` : `UNTRUSTED_RESEARCHER_PROOF_CARRYING_EVIDENCE_PASS`.
- `labs/untrusted_trace_results_20261117/proof_status.txt` : `lean_main_exit=0`, `lean_mutated_label_exit=1`, `lean_mutated_coordinate_exit=1`.
- `labs/untrusted_trace_results_20261117/TraceCertificate.lean`, `lean_positive.log` et journaux des mutations.

**Conclusion exacte :** il n'est plus nécessaire de faire confiance au calcul Python du chercheur pour établir la concordance **entre les réponses enregistrées et les polynômes** et **entre les deux représentations algébriques**, sous réserve de vérifier l'authenticité des réponses d'origine par le mécanisme d'audit indépendant. Les hypothèses sur les lois inconnues restent explicites, et leurs conclusions globales sont refusées hors domaine de validité.
