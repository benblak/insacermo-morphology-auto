# INSACERMO Morphology Auto Detector V28.0.0

**Benjamin Lenoir - INSACERMO, Rennes, France**  
ORCID: 0009-0006-1201-7127

V28 analyse automatiquement des journaux d'entraînement CSV reconnus.

## Fonctions

- détection des colonnes temporelles ;
- reconnaissance des losses et métriques de performance ;
- orientation minimiser/maximiser ;
- détection d'une validation trop rare ;
- fenêtre adaptative ;
- morphologie actuelle dominante ;
- fermeture cachée ;
- confiance et statut de verrouillage ;
- transitions de régime ;
- alertes GREEN / YELLOW / ORANGE / RED ;
- détection `UNKNOWN_NOVEL`.

## Installation

```bash
python -m pip install -r requirements.txt
```

## Test rapide

```bash
python insacermo_morphology_auto_v28.py synthetic_overfit_log.csv
```

## Principe

```text
D_hidden = 1 - H_morph / (H_micro + epsilon)
```

La fermeture cachée mesure le degré de concentration.  
La morphologie dominante indique la direction de cette concentration.

## Portée

V28.0.0 est un détecteur pour les formats de logs reconnus. Il ne constitue pas
encore un contrôleur autonome validé pour arrêter ou modifier un entraînement
sans vérification humaine.

## Licence

Code : Apache License 2.0.  
Le nom INSACERMO désigne le programme de recherche de Benjamin Lenoir.

Voir `CITATION.cff` pour citer le logiciel.


## DOI officiels

- Logiciel V28.0.0 : [10.5281/zenodo.20852518](https://doi.org/10.5281/zenodo.20852518)
- Document scientifique associé : [10.5281/zenodo.20851280](https://doi.org/10.5281/zenodo.20851280)

## Citation rapide

```text
Benjamin Lenoir (2026). INSACERMO Morphology Auto Detector
(Version 28.0.0). Zenodo. https://doi.org/10.5281/zenodo.20852518
```
