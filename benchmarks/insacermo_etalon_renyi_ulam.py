#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""INSACERMO — Étalon Rényi–Ulam / OpenFlights à 5 mondes.

Audit indépendant, sans bibliothèque externe et sans entraînement statistique.
Exécution : python3 insacermo_etalon_renyi_ulam.py

Contrat et limites :
  mondes = {0 (réseau intact), 1, 2, 3, 4 (panne de la liaison i)} ;
  au plus 3 réponses erronées au total (adversaire) ;
  sonde i = question « la liaison i est-elle en panne ? » ;
  identification = isoler l'un des 5 mondes ;
  réparation ciblée = une action de réparation de la liaison i restaure
    le service si le réseau est intact ou si i est la liaison en panne ;
  réparation générale = action toujours sûre, coût 24 ;
  coût sonde = 1 ; coût réparation ciblée = 2.

Les algorithmes prennent le pire cas sur toutes les réponses admissibles,
mettent en mémoire les états et donnent des minima exacts DANS CE MODELE.
Ni les pannes physiques ni le code Lean ne sont validés ici.

Note: « question libre » signifie que chaque question oui/non peut désigner
n'importe quel sous-ensemble des 5 mondes. « sonde limitée » signifie que
seules les 4 questions sur les liaisons individuelles sont autorisées.
"""
from functools import lru_cache

N = 5
E = 3
DEAD = E + 1
INIT = (0,) * N

def vivants(etat):
    """Hypothèses dont le nombre d'erreurs ne dépasse pas E."""
    return tuple(i for i, err in enumerate(etat) if err <= E)

def mise_a_jour(etat, masque, reponse):
    """Met à jour les compteurs d'erreurs de chaque hypothèse."""
    return tuple(
        min(DEAD, err + (int(bool(masque & (1 << monde))) != reponse))
        for monde, err in enumerate(etat)
    )

def fin(etat, contrat):
    mondes = vivants(etat)
    if contrat == 'identifier':
        return len(mondes) <= 1
    if contrat == 'reparer':
        return sum(monde != 0 for monde in mondes) <= 1
    raise ValueError(contrat)

SONDES_LIMITEES = tuple(1 << i for i in range(1, N))
SONDES_LIBRES = tuple(range(1, 1 << (N - 1)))

@lru_cache(maxsize=None)
def possible_en_k(etat, k, contrat, sondes):
    """Existe-t-il un arbre de sondes de profondeur <= k, contre tous mensonges ?"""
    if fin(etat, contrat):
        return True
    if k == 0:
        return False
    for masque in sondes:
        branches = [mise_a_jour(etat, masque, reponse) for reponse in (0, 1)]
        if etat in branches:
            continue
        if all(
            possible_en_k(suivant, k - 1, contrat, sondes)
            for suivant in branches if vivants(suivant)
        ):
            return True
    return False

def profondeur_optimale(contrat, sondes, plafond=50):
    for k in range(plafond + 1):
        if possible_en_k(INIT, k, contrat, sondes):
            assert k == 0 or not possible_en_k(INIT, k - 1, contrat, sondes)
            return k
    raise RuntimeError('Plafond insuffisant')

@lru_cache(maxsize=None)
def cout_optimal(etat):
    """Coût minimax, avec action ciblée ou générale, et questions limitées."""
    if fin(etat, 'reparer'):
        return 0 if vivants(etat) == (0,) else 2
    meilleure_borne = 24
    for masque in SONDES_LIMITEES:
        branches = [mise_a_jour(etat, masque, reponse) for reponse in (0, 1)]
        if etat in branches:
            continue
        cout = 1 + max(
            cout_optimal(suivant) for suivant in branches if vivants(suivant)
        )
        meilleure_borne = min(meilleure_borne, cout)
    return meilleure_borne

def cout_fixe_identification():
    return (N - 1) * (2 * E + 1)

def audit():
    resultats = {
        'fixe_identification': cout_fixe_identification(),
        'adaptatif_identification': profondeur_optimale('identifier', SONDES_LIMITEES),
        'adaptatif_reparation': profondeur_optimale('reparer', SONDES_LIMITEES),
        'libre_classique_identification': profondeur_optimale('identifier', SONDES_LIBRES),
        'cout_minimax_reparation': cout_optimal(INIT),
    }
    attentes = {
        'fixe_identification': 28,
        'adaptatif_identification': 19,
        'adaptatif_reparation': 15,
        'libre_classique_identification': 12,
        'cout_minimax_reparation': 17,
    }
    for nom, valeur in resultats.items():
        statut = 'OK' if valeur == attentes[nom] else 'ECHEC'
        print(f'{statut:5}  {nom:38} {valeur:2} (attendu {attentes[nom]})')
    assert resultats == attentes, 'Les résultats ne correspondent pas aux attentes'
    print('\nPASS : vérification exacte des minima dans le modèle spécifié.')
    print('Limites : non-compilation Lean, absence de mesure terrain et de preuve')
    print('de nouveauté scientifique générale dans ce fichier.')

if __name__ == '__main__':
    audit()
