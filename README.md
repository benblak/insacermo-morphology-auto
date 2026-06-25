{
  "version": "V28",
  "principle": "dominant morphology + hidden closure + confidence + chronology",
  "labels": {
    "FAVORABLE": "Training and validation improve together.",
    "FAVORABLE_GAP_WARNING": "Training and validation improve while their gap widens.",
    "OVERFIT_DRIFT": "Training improves while validation degrades.",
    "DEGRADATION": "Training and validation degrade together.",
    "IMPROVING_TRAIN_ONLY": "Training metric improves without sufficient validation reference.",
    "WORSENING_TRAIN_ONLY": "Training metric degrades without sufficient validation reference.",
    "PLATEAU": "Net movement is below the automatically calibrated activity threshold.",
    "MIXED": "Train/validation geometry is inconsistent.",
    "UNKNOWN_NOVEL": "No frozen grammar matches the observed multimetric direction."
  }
}