# INSACERMO V2 — Détecteur aveugle de ruptures structurelles sur la carte logistique

**Date de gel :** 20 septembre 2026  
**Statut :** protocole exploratoire gelé avant lecture des résultats  
**Core V1 gelé modifié :** NON

## Question

À partir uniquement des complexes de futurs calculés par INSACERMO sur

[
x_{t+1}=r x_t(1-x_t),
]

peut-on localiser des changements structurels dans l’espace des futurs **sans fournir au moteur les valeurs connues des bifurcations** ?

## Dynamique et grille

- (rin[2.8,4.0])
- pas fixe : (0.001)
- 1024 conditions initiales déterministes ((i+1/2)/1024)
- 1500 itérations de burn-in
- horizon futur : 12 pas

## Trois contrats figés avant résultat

Pour chaque seuil (cin{0.4,0.5,0.6}), et chaque offset (j=1,ldots,12), définir

[
q_{j,c}: x_{t+j}ge c.
]

Chaque seuil définit son propre complexe de futurs réalisables. Aucun seuil n’est ajusté après résultat.

## Distance structurelle primaire

Pour deux paramètres adjacents (r_i,r_{i+1}), soit (K_c(r)) l’ensemble exact des paquets réalisables parmi les (2^{12}=4096) paquets du contrat (c).

Définir

[
J_c(r_i)=rac{|K_c(r_i)	riangle K_c(r_{i+1})|}{4096}.
]

C’est une distance exacte de différence symétrique entre deux complexes finis.

Le score consensus est gelé comme la médiane des trois contrats :

[
oxed{J_{mathrm{cons}}(r_i)=operatorname{median}(J_{0.4},J_{0.5},J_{0.6}).}
]

## Détection aveugle

Les valeurs classiques de bifurcation ne sont pas accessibles à l’algorithme de détection.

Étapes :

1. calculer toute la série (J_{mathrm{cons}}) ;
2. trouver tous les maxima locaux strictement positifs ;
3. les trier par score décroissant ;
4. appliquer une suppression non maximale fixe de rayon (0.004) en (r) ;
5. conserver les 25 premiers pics.

Seulement **après** cette liste gelée, comparer descriptivement aux repères classiques :

- (r=3)
- (1+sqrt6)
- 3.544090359
- 3.564407266
- 3.569945672
- (1+sqrt8)

Un repère est dit “proche” si un pic est à distance absolue (le0.01). Cette tolérance est gelée avant résultat et ne constitue pas une p-value.

## Contrôles

Le rapport doit aussi montrer, pour chaque repère connu, les trois scores contractuels séparés. Une absence de pic pour certains seuils est un résultat valide et illustre la dépendance au contrat.

## Images déterministes

Deux SVG seront produits :

1. **BLIND** : uniquement la courbe (J_{mathrm{cons}}) et les pics détectés ; aucun repère classique.
2. **AUDIT** : même sortie, puis ajout des repères classiques après détection.

Aucun modèle de génération d’images n’est utilisé.

## Limites

Ce test ne prétend pas détecter “le chaos” universellement. Il teste si une géométrie contractuelle de futurs change près de transitions dynamiques connues, et si cette visibilité dépend du contrat.
