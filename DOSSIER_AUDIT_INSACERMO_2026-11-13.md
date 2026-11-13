# INSACERMO — DOSSIER D'AUDIT CERTIFIÉ (13 novembre 2026)

**Une phrase :** INSACERMO étudie ce qu'il faut observer pour garantir une action, et peut prouver qu'une quantité moindre d'information est insuffisante dans un problème fini déclaré.

Ceci est un **paquet de laboratoire indépendant**, pas une nouvelle version du moteur INSACERMO MAX TOTAL/C3. Le noyau, les archives historiques et le site restent figés.

## Démarrer en moins de deux minutes

Pour contrôler uniquement les calculs Python (aucune dépendance) :

```bash
python3 berge_core_audit/five_world_probe_audit.py
python3 benchmarks/insacermo_etalon_renyi_ulam.py
```

Pour refaire les preuves, ouvrir **Actions** sur ce dépôt et consulter les runs ci-dessous. Les deux projets Lean utilisent **Lean 4.20.0** ; le principal ne dépend pas de Mathlib.

## Les trois dossiers importants

| Dossier | Contenu | Garantie |
|---|---|---|
| `berge_core_audit/` | Théorème de Berge (mise à jour des transversaux), descente finie, observation binaire, conservation exacte des obstructions et minimum de 3 sondes, workflows, test 512 cas | Preuves Lean 4.20 + contrôle externe lean4checker (run 43437488745) |
| `berge_lean420_audit/` | Reconstruction précédente des obstructions et du critère par fibres avec Mathlib | Lean 4.20, run 43425229350 |
| `benchmarks/` | Étalon Rényi–Ulam à cinq mondes, **trois mensonges** possibles | Minima exacts dans ce modèle par programmation dynamique Python, non prouvés ici en Lean |

Les fichiers des démonstrations sont **des reconstructions indépendantes**, et NON le fichier original `InsacermoBerge.lean` de Claude. L'énoncé original `κ ≤ |C|` n'a pas été formalisé ni vérifié dans ce paquet.

## Résultats précis et séparés

### A. Observations binaires fiables — **aucun mensonge**

Modèle fini : cinq mondes `0,1,2,3,4`. Quatre sondes binaires individuelles `1..4`. Une réparation ciblée `i` est sûre dans les mondes `0` et `i`.

- **0, 1 ou 2 sondes distinctes : impossible** de garantir une réparation ciblée dans tous les cas.
- **3 sondes distinctes : suffisant et optimal**.
- L'énoncé `exact_minimum_three` est compilé dans Lean 4.20, recontrôlé par `lean4checker` (run **43437488745**, commit `db0f8e93f5fc6e900e727168496f420e83943047`).
- Le test exhaustif indépendant recalcule les 16 choix de sous-ensembles de sondes sur les 32 sous-ensembles de mondes : **512 vérifications**, aucune contradiction.
- Pour les obstructions minimales : 6 avant sondage, puis 3, 1, 0 après 1, 2, 3 sondes distinctes.

**Limites :** questions non mensongères, sondes présélectionnées et sélection non adaptative ; quatre pannes abstraites et aucune mesure terrain de coût, d'énergie ou de fiabilité. Les classes réelles de panne sont réduites à une abstraction.

### B. Théorèmes structuraux Lean (sans Mathlib)

- `finite_descent` : extraction par descente finie (si un rang naturel décroît strictement avec les inclusions strictes).
- `berge_update_iff` : mise à jour des transversaux minimaux lors de l'ajout d'une hyperarête, dans la sémantique déclarée.
- `new_obstruction_contains_old` : une nouvelle obstruction minimale contient une ancienne lorsque les actions disponibles augmentent. **Cela ne dit PAS que les anciennes obstructions persistent.**
- `obs_feas_iff` : faisabilité équivalente à la faisabilité sur chaque fibre d'une observation fiable.
- `obs_minimal_iff_old_minimal_monochromatic` : les obstructions minimales après observation sont exactement les anciennes qui ne sont pas séparées.
- `raises_order_iff_splits_critical` et `library_blockage_certificate` : critère exact pour relever l'ordre minimal et certificat qu'aucune sonde de la bibliothèque, **prise seule**, ne convient.

Lean utilise uniquement les axiomes standard déclarés (`propext`, `Classical.choice`, `Quot.sound`, ou aucun selon le théorème). **Pas de `sorryAx`.** On ne revendique pas que les résultats sont nouveaux dans la littérature (Berge, 2-coloration d'hypergraphes et identification active sont des domaines existants).

### C. Étalon avec **jusqu'à trois réponses erronées**

Le programme Python séparé donne pour le modèle spécifié :
- Identification, sondes fixes : **28** questions (preuve combinatoire des 7 répétitions par liaison dans le modèle).
- Identification, sondes limitées adaptatives : **19** questions au pire.
- Action sûre, sondes limitées adaptatives : **15** questions au pire.
- Identification, questions binaires libres : **12** questions au pire.
- Coût minimax réparation avec coûts sondes=1, réparation ciblée=2 et réparation générale=24 : **17**.

Ne pas comparer directement « 3 sondes fiables » à « 15 questions avec 3 mensonges » : les deux contrats et hypothèses diffèrent. Les chiffres 28→19 et 28→15 n'ont pas la même signification. Le tableau fixe/adaptatif 2×2 présenté par Claude incluait aussi 15 sondes fixes pour l'action ; **son fichier d'énumération `INSACERMO_etalon_2x2.py` n'est pas inclus, ni revendiqué comme audité dans ce paquet.**

## Références de traçabilité

- [Run Lean/lean4checker + minimum de 3 sondes 43437488745](https://github.com/benblak/insacermo-morphology-auto/actions/runs/43437488745)
- [Run Lean/lean4checker + critère de séparation 43436284491](https://github.com/benblak/insacermo-morphology-auto/actions/runs/43436284491)
- [Run Lean/lean4checker + Berge/descente 43428649926](https://github.com/benblak/insacermo-morphology-auto/actions/runs/43428649926)
- [Run Lean/Mathlib précédent 43425229350](https://github.com/benblak/insacermo-morphology-auto/actions/runs/43425229350)
- Branche d'audit : `audit/insacermo-certified-package-20261113`
- Tous ces audits sont séparés de la branche de production.

## Pour qui reçoit ce ZIP

1. Exécuter les deux scripts Python ci-dessus et lire les résultats.
2. Avec Lean 4.20, aller dans `berge_core_audit` puis `lake update && lake build` ; le workflow GitHub exécute en outre `lean4checker`.
3. Pour `berge_lean420_audit` : `lake update && lake exe cache get && lake env lean InsacermoBerge.lean` (nécessite Mathlib).
4. Vérifier les **énoncés exacts** et les hypothèses : ils certifient des modèles finis ou conditionnels, pas tout INSACERMO ni l'original de Claude.
5. Comparer avec la littérature sur Berge, les transversaux minimaux, la propriété B, la sélection de sondes et Rényi–Ulam avant de revendiquer une nouveauté.

**Formulation publique recommandée :**
> « INSACERMO — instrument expérimental de décision logique : il recherche des actions garanties et les informations minimales nécessaires, et fournit des preuves d'optimalité ou d'impossibilité dans des modèles finis déclarés. Plusieurs résultats ont été formalisés sous Lean 4.20 et contrôlés indépendamment. »

**À ne pas dire :** « intelligence universelle », « découverte physique », « tous les résultats d'INSACERMO prouvés par Lean », ou « loi de Berge nouvelle ».
