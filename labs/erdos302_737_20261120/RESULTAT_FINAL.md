# INSACERMO: un seul résultat fini pour Erdős #302

**Problème (restant ouvert en général).** Notons `f(N)` la taille maximale d'un ensemble de nombres entiers distincts choisis dans `{1,...,N}` ne contenant aucun triplet distinct `a,b,c` tel que `1/a=1/b+1/c`.

## Résultat

**Pour N=737, f(737)=f(736)+1.**

C'est une récurrence exacte, mais **pas** une valeur numérique absolue de `f(737)` tant qu'une valeur certifiée de `f(736)` n'est pas fournie.

### Démonstration élémentaire

La seule façon d'introduire une nouvelle relation interdite en passant de 736 à 737 serait d'utiliser 737 dans un triplet. Dans une telle identité de fractions unitaires positives, le dénominateur du membre de gauche est le plus petit : écrivons donc `1/a=1/c+1/737`, avec `1 <= a < c < 737`.

L'identité se réécrit `737a=c(737-a)`, puis `(737-a)(737+c)=737²`. Posons `d=737-a`. Puisque `a<c<737`, `369 <= d <=736`, et `d` doit diviser `737²`.

Or `737=11×67`, et les seuls diviseurs positifs de `737²` sont `1,11,67,121,737,4489,8107,49379,543169`. **Aucun ne se situe entre 369 et 736.** Donc il n'existe pas de nouveau triplet avec 737.

Toute solution admissible pour 736 reste admissible quand on y ajoute 737 ; ainsi `f(737)>=f(736)+1`. Inversement, enlever 737 à tout ensemble admissible pour 737 laisse un ensemble de taille au plus `f(736)` ; ainsi `f(737)<=f(736)+1`. D'où l'égalité.

### Vérification informatique indépendante

- `Erdos302_737.lean` compile avec Lean 4.33.1 : absence de tout `a` susceptible de former un nouveau triplet et absence de diviseur de `737²` dans l'intervalle critique ;
- `audit_737.py` retrouve indépendamment la liste des neuf diviseurs, le vide de l'intervalle critique et l'absence de triplets ;
- GitHub Actions trace la compilation et refuse `sorry`, `admit` et `axiom` dans le nouveau fichier Lean.

**Portée :** résultat arithmétique fini élémentaire. Aucun progrès établi sur l'asymptotique ouverte d'Erdős #302 ; aucune priorité historique ni originalité de l'argument général n'est revendiquée sans contrôle indépendant. Les deux preuves Lean certifient les tests finis indiqués, tandis que la déduction extremale est donnée ci-dessus comme démonstration mathématique explicite, non comme théorème Lean end-to-end.

**Projet INSACERMO :** noyau C3 et archives historiques inchangés ; cette pièce est un laboratoire séparé et clos.
