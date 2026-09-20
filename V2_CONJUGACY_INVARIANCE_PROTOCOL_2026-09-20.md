# INSACERMO V2 — Audit d'invariance par conjugaison : logistique r=4 vs tente pente 2

**Date de gel :** 20 septembre 2026  
**Statut :** protocole exploratoire gelé avant résultat  
**Core V1 gelé modifié :** NON

## Question

La géométrie de futurs calculée par INSACERMO dépend-elle seulement des coordonnées utilisées pour écrire le système, ou peut-elle être conservée sous une conjugaison dynamique lorsqu'on transporte aussi le contrat ?

Test classique :

[
L(x)=4x(1-x)
]

et carte tente

[
T(y)=1-|1-2y|.
]

Elles sont reliées par

[
h(y)=sin^2(pi y/2),
]

avec

[
L(h(y))=h(T(y)).
]

De plus, comme (h) est croissante sur ([0,1]),

[
xge 1/2 iff yge 1/2.
]

Ainsi le contrat binaire futur (q_j:z_{t+j}ge1/2) est transporté naturellement par la conjugaison.

## Protocole figé

- 4096 graines déterministes (y_i=(i+1/2)/4096)
- graines logistiques (x_i=h(y_i))
- aucun burn-in
- horizon symbolique K=16
- contrat : (q_j:z_{t+j}ge1/2), j=1..16
- calcul séparé des signatures symboliques de la carte logistique et de la carte tente
- construction du complexe exact des paquets réalisables par fermeture descendante
- comparaison :
  1. signatures observées ;
  2. complexe des futurs réalisables ;
  3. obstructions minimales par rang ;
  4. facettes maximales ;
  5. empreinte déterministe rendue depuis le complexe.

## Tolérance

Aucune tolérance n'est autorisée pour la comparaison des complexes : ils doivent être identiques bit à bit pour PASS.

Les signatures individuelles peuvent différer pour quelques graines à cause de l'arithmétique flottante ; ce nombre est rapporté, mais le critère principal reste l'égalité exacte du complexe obtenu.

## Contrôle négatif figé

Comparer aussi la carte logistique (r=3.9) au même système tente pente 2, avec les mêmes graines/contrats.

Le contrôle négatif doit produire un complexe différent. S'il est identique, le test n'est pas discriminant.

## Interprétation

PASS fort :

[
K_{	ext{logistique }4}=K_{	ext{tente }2}
]

mais

[
K_{	ext{logistique }3.9}
e K_{	ext{tente }2}.
]

Cela montrerait que, dans ce cas, l'objet INSACERMO capturé par ce contrat est invariant sous une conjugaison connue et ne se réduit pas à la forme graphique des coordonnées.

Cela ne prouve pas une invariance générale du Core sous toute conjugaison : ce serait un exemple exact fini sous ce contrat.
