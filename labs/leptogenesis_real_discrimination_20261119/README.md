# INSACERMO — Discrimination conditionnelle de deux modèles de leptogenèse publiés
**Laboratoire séparé, 19 novembre 2026.** Branche: `lab/antimatter-two-published-models-20261119`.

## Statut
- GitHub Actions **SUCCESS**, run [44613566264](https://github.com/benblak/insacermo-morphology-auto/actions/runs/44613566264), commit `2ba46715018223576756b88063426bb266a04f55`.
- Lean 4.33.1: compilation du noyau portable C3 historique et de `PublishedPhaseSeparation.lean`; aucun `sorry`, `admit`, nouvel `axiom` dans les deux fichiers formels du laboratoire.
- Le C3 d'origine `insacermo_one_engine.py` reste byte-identique au Git blob `bd5310b3692bcbad4e874005b7dd8eda90616f74`.
- Trois certificats C3 produits et rejoués par Lean: `NO_MEASUREMENT` → `REFUSE_ROBUST`; `IDEAL_PHASE_PROBE_BOUND_47` → `PROBE`; `NEW_RIVAL_SAME_PHASE_SIGNAL` → `REFUSE_ROBUST`.
- Audit séparé Python sur le cercle discret de 360°: aucun chevauchement des observations admissibles pour erreur entière ≤47°, chevauchement à 48°.

## Données scientifiques en entrée
Deux familles de prédictions pour la phase leptonic Dirac CP, modulo 360°, prises de **modèles théoriques distincts publiés**, pas de mesures expérimentales:
- **A** (leptogenèse, 2018): `δCP ∈ [198°,225°]`.
- **B** (modèle modulaire A4, 2021): `δCP ∈ [5°,40°] ∪ [320°,355°]`.
Ces domaines sont sous les hypothèses de chaque article. Ils ne sont PAS des prédictions universelles de la leptogenèse.
Contexte observationnel: l'ajustement global préliminaire Bari 2026.a recouvre encore les régions de A et de la branche haute de B à 3 sigma. Une valeur centrale seule n'est pas une preuve d'exclusion.

## Théorème exact vérifié
Pour des angles vrais `pA` dans A et `pB` dans B, et une mesure `z` dans `[0,360)`, si le modèle d'erreur **déterministe circulaire** certifie simultanément
`dist_circle(pA,z) ≤ 47°` et `dist_circle(pB,z) ≤ 47°`, alors il y a contradiction.

L'écart circulaire minimal entre les deux régions publiées est **95°** (A:225°, B:320°). Par l'inégalité triangulaire, un risque de confusion nul pour l'un de ces deux modèles exige une erreur maximale **strictement inférieure à 47,5°**. À la granularité entière de ce banc, **±47° fonctionne**; **±48° ne garantit plus la séparation**. Contre-exemple formalisé: modèle A vrai 225°, modèle B vrai 320°, mesure z=272°.

Le résultat est une **condition cible de performance**, PAS une mesure publiée de DUNE, Hyper-Kamiokande, ni une signification statistique. Aucun instrument réel n'a été déclaré atteindre cette borne d'erreur déterministe. Des prévisions d'erreur fréquentistes ne doivent pas être remplacées par une borne absolue.

## C3 — sens opérationnel
Le contrat `identify A vs B` repose sur 3 mondes abstraits: A, branche B basse et branche B haute. La sonde binaire est une **abstraction** du résultat d'une mesure de phase certifiée à ±47°, et non une expérience physique exécutée:
- Sans sonde: refus, car A et B exigent des actions distinctes.
- Avec la sonde conditionnelle: PROBE, puis action A ou B selon le résultat.
- En ajoutant un rival hors catalogue qui produit le même signal que A: refus, donc la garantie dépend de la **complétude du catalogue**.

Les preuves Lean ne certifient ni la validité des modèles publiés, ni leur fidélité au monde, ni le caractère exhaustif des hypothèses, ni une identification de la cause cosmique de la baryogenèse.

## Rejouer
```bash
# Lean 4.33.1, répertoire de dépôt en cours
export LEAN_PATH=.:lean
lean -o C3/PortableFiniteVerifierV1.olean C3/PortableFiniteVerifierV1.lean
lean -o C3/PortableVerifierSoundnessV1.olean C3/PortableVerifierSoundnessV1.lean
lean -o C3/PortableExactSearchV1.olean C3/PortableExactSearchV1.lean
lean -o labs/refus_espoir_20261119/RefusEspoirBridge.olean labs/refus_espoir_20261119/RefusEspoirBridge.lean
lean labs/leptogenesis_real_discrimination_20261119/PublishedPhaseSeparation.lean
PYTHONPATH=. python3 labs/leptogenesis_real_discrimination_20261119/audit_published_phase.py
```

## Étape non réalisée
Ne PAS recommander de construire un télescope ou détecteur sur la seule borne géométrique. Il reste à confronter les vraies performances et systématiques de DUNE/Hyper-Kamiokande, le cas où ni A ni B n'est vrai, les données d'oscillation jointes, et des modèles rivalisant sur plusieurs observables. Le résultat présente une condition quantitative à tester, pas une découverte astrophysique.
