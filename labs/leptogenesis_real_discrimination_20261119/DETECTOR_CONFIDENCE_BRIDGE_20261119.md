# INSACERMO — continuation du même laboratoire : précision des détecteurs (19/11/2026)

## Périmètre et traçabilité

Continuation de `labs/leptogenesis_real_discrimination_20261119/`, sans modification de `insacermo_one_engine.py` ni des preuves Lean historiques. Le run GitHub Actions 44613821166 reste la validation de la **séparation déterministe conditionnelle** à ±47°, PAS une validation des performances physiques des détecteurs ni de ce pont statistique.

**Sources des domaines de phases :**
- A : *Neutrino phenomenology from leptogenesis* (EPJC 2018), https://doi.org/10.1140/epjc/s10052-018-6299-6. Phase δ entre −0.90π et −0.75π (soit 198°–225° modulo 360, bornes arrondies).
- B : *Modulus τ linking leptonic CP violation to baryon asymmetry in A4 modular invariant flavor model* (JHEP 2021), https://doi.org/10.1007/JHEP07(2021)184. Sous ses hypothèses de BAU, [5°,40°] et [320°,355°].

**Sources des performances simulées publiées :**
- Hyper-Kamiokande Collaboration (2026), https://doi.org/10.1140/epjc/s10052-025-14938-9 : résolution de phase annoncée ~6°–20° selon la vraie phase, après dix ans, estimation à 1σ.
- DUNE, contribution au programme scientifique ESPPU 2026, https://indico.global/event/14242/contributions/122913/attachments/57613/110664/DUNE_Science_ESPPU2026_v6.pdf : précisions projetées, valeurs les plus défavorables 27° / 22° / 18° pour des expositions respectives de 300 / 600 / 1000 kt·MW·an. Pour le seul calcul de sensibilité ci-dessous, **on suppose** que ces « précisions » peuvent servir d'écart-type sigma d'une erreur gaussienne centrée; le document ne garantit pas ce modèle probabiliste.

## Test calculable (pas de nouveau théorème Lean)

On suppose artificiellement une erreur de mesure gaussienne centrée de sigma degrés et on construit un intervalle symétrique de confiance de niveau c, de demi-largeur r = sigma × Φ⁻¹((1+c)/2). Si **r < 47,5°**, la région de phase ainsi construite ne peut intersecter à la fois A et B, quelle que soit la valeur centrale. Un intervalle de confiance n'est pas une garantie d'erreur absolue.

| Scénario (sigma défavorable) | Niveau supposé | Demi-largeur r | Angles centraux entiers ambigus parmi 360 |
| --- | ---: | ---: | ---: |
| DUNE 2026, 300 kt·MW·an, sigma = 27° | 95 % | 52,92° | 10 |
| DUNE 2026, 600 kt·MW·an, sigma = 22° | 95 % | 43,12° | 0 |
| DUNE 2026, 600 kt·MW·an, sigma = 22° | 99 % | 56,67° | 18 |
| DUNE 2026, 1000 kt·MW·an, sigma = 18° | 99 % | 46,36° | 0 |
| Hyper-K 2026, sigma = 20° | 95 % | 39,20° | 0 |
| Hyper-K 2026, sigma = 20° | 99 % | 51,52° | 8 |

Les nombres de centres ambigus proviennent d'une énumération exhaustive de 360 centres **entiers**: ils ne sont ni des probabilités d'observation ni des erreurs de classification mesurées. La séparation est mathématique; le passage de « résolution projetée » à « niveau de confiance » dépend de l'approximation gaussienne, qui n'a pas été validée par les données brutes.

Ensemble mesuré intersectant A seul → A_ONLY; B seul → B_ONLY; A et B → BOTH (ambigu); aucun → NEITHER (catalogue possiblement incomplet). Ces labels sont **diagnostiques du script**, pas de nouveaux verdicts ajoutés à C3.

## Rejeu

```bash
python3 labs/leptogenesis_real_discrimination_20261119/phase_confidence_bridge_20261119.py
```

Résultat attendu : `CONDITIONAL_GAUSSIAN_PROXY_TESTS_SUCCESS`. Le script est autonome et n'appelle pas Lean. La preuve Lean historique établit le cas **déterministe** d'erreur ≤47°, et un contre-exemple pour 48°. Aucun nouveau run Lean ni nouvelle compilation GitHub Actions n'est revendiqué pour les proxies statistiques.

## Conclusion et prochain critère

En 2026, les deux projets annoncent des sensibilités qui motivent le test, mais le certificat C3 « discrimination sans erreur » reste conditionné à une véritable borne d'erreur absolue. Une future confrontation expérimentale robuste nécessite les **courbes de vraisemblance profilées** (incluant systématiques, octant, ordre des masses et multimodalité éventuelle) pour les zones publiées A et B, pas seulement les résolutions globales.
