#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 Benjamin Lenoir
# INSACERMO Morphology Auto Detector V28.0.0
"""
INSACERMO Morphology Auto Detector V28
Benjamin Lenoir — INSACERMO, Rennes, France

Generic offline detector for training-log CSV files.
It automatically identifies useful metric columns, their optimization direction,
window morphology, dominant morphology, regime transitions, hidden closure,
confidence, and chronological organization against increment-permutation controls.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import re
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Any

import numpy as np
import pandas as pd

try:
    import matplotlib.pyplot as plt
except Exception:
    plt = None


VERSION = "INSACERMO_MORPHOLOGY_AUTO_V28"
DEFAULT_SEED = 20260625

TIME_PATTERNS = [
    r"^step$", r"^epoch$", r"time", r"elapsed", r"timestamp", r"iteration", r"iter"
]
IGNORE_PATTERNS = [
    r"learning.?rate", r"^lr$", r"wall.?time", r"elapsed", r"timestamp",
    r"batch", r"seed", r"gpu", r"memory", r"throughput"
]

LOWER_BETTER_PATTERNS = [
    r"loss", r"error", r"perplex", r"ppl", r"wer", r"cer", r"rmse", r"mae",
    r"mse", r"distance", r"latency", r"cost"
]
HIGHER_BETTER_PATTERNS = [
    r"acc", r"accuracy", r"f1", r"auc", r"precision", r"recall", r"reward",
    r"score", r"bleu", r"rouge", r"map", r"success"
]
TRAIN_PATTERNS = [r"train", r"training", r"^loss$"]
VALIDATION_PATTERNS = [r"val", r"eval", r"valid", r"test"]


@dataclass
class MetricSpec:
    column: str
    role: str
    direction: str
    coverage: float
    source: str


def matches_any(name: str, patterns: list[str]) -> bool:
    value = name.lower().strip()
    return any(re.search(pattern, value) for pattern in patterns)


def robust_center_scale(values: np.ndarray) -> tuple[float, float]:
    clean = values[np.isfinite(values)]
    if len(clean) == 0:
        return 0.0, 1.0
    median = float(np.median(clean))
    mad = float(1.4826 * np.median(np.abs(clean - median)))
    std = float(np.std(clean))
    scale = mad if mad > 1e-12 else std if std > 1e-12 else 1.0
    return median, scale


def normalize_label(value: str) -> str:
    return re.sub(r"[^a-z0-9]+", "_", value.lower()).strip("_")


def identify_time_column(df: pd.DataFrame) -> str | None:
    candidates = []
    for column in df.columns:
        if pd.api.types.is_numeric_dtype(df[column]) and matches_any(column, TIME_PATTERNS):
            score = 0
            name = column.lower()
            if name == "step":
                score += 5
            if name == "epoch":
                score += 4
            if "time" in name:
                score += 2
            monotonic = df[column].dropna().is_monotonic_increasing
            if monotonic:
                score += 3
            candidates.append((score, column))
    if not candidates:
        return None
    return max(candidates)[1]


def infer_metric_specs(df: pd.DataFrame) -> tuple[list[MetricSpec], str | None, list[str]]:
    time_column = identify_time_column(df)
    specs: list[MetricSpec] = []
    excluded: list[str] = []

    for column in df.columns:
        series = pd.to_numeric(df[column], errors="coerce")
        coverage = float(series.notna().mean())

        if column == time_column:
            excluded.append(column)
            continue
        if not pd.api.types.is_numeric_dtype(series):
            excluded.append(column)
            continue
        if matches_any(column, IGNORE_PATTERNS):
            excluded.append(column)
            continue
        if coverage < 0.18 or series.nunique(dropna=True) < 3:
            excluded.append(column)
            continue

        lower = matches_any(column, LOWER_BETTER_PATTERNS)
        higher = matches_any(column, HIGHER_BETTER_PATTERNS)
        train = matches_any(column, TRAIN_PATTERNS)
        validation = matches_any(column, VALIDATION_PATTERNS)

        if lower:
            direction = "LOWER_IS_BETTER"
        elif higher:
            direction = "HIGHER_IS_BETTER"
        else:
            direction = "UNKNOWN_DIRECTION"

        if train and lower:
            role = "TRAIN_COST"
        elif validation and lower:
            role = "VALIDATION_COST"
        elif train and higher:
            role = "TRAIN_PERFORMANCE"
        elif validation and higher:
            role = "VALIDATION_PERFORMANCE"
        elif lower:
            role = "GENERIC_COST"
        elif higher:
            role = "GENERIC_PERFORMANCE"
        else:
            role = "GENERIC_SIGNAL"

        specs.append(
            MetricSpec(
                column=column,
                role=role,
                direction=direction,
                coverage=coverage,
                source="AUTO_SCHEMA",
            )
        )

    return specs, time_column, excluded


def choose_window_length(n_rows: int, requested: int | None) -> int:
    if requested is not None:
        if requested < 3:
            raise ValueError("Window length must be at least 3.")
        if requested > n_rows:
            raise ValueError("Window length exceeds the number of usable rows.")
        return requested

    # Adaptive but conservative: 5 for short logs, slowly increasing for long logs.
    estimate = int(round(n_rows / 12))
    window = max(5, min(15, estimate))
    if n_rows - window + 1 < 6:
        window = max(3, n_rows - 5)
    return window


def prepare_matrix(
    df: pd.DataFrame, specs: list[MetricSpec], min_validation_coverage: float
) -> tuple[pd.DataFrame, list[MetricSpec], dict[str, Any]]:
    work = pd.DataFrame(index=df.index)
    retained: list[MetricSpec] = []
    sparse_validation: list[str] = []

    for spec in specs:
        series = pd.to_numeric(df[spec.column], errors="coerce")
        is_validation = spec.role.startswith("VALIDATION")
        if is_validation and spec.coverage < min_validation_coverage:
            sparse_validation.append(spec.column)
            continue

        if series.notna().sum() < 4:
            continue

        # Interpolate internal gaps only when enough observations exist.
        series = series.interpolate(limit_direction="both")
        if series.notna().all():
            work[spec.column] = series.astype(float)
            retained.append(spec)

    metadata = {
        "sparse_validation_columns": sparse_validation,
        "usable_metric_count": len(retained),
        "usable_row_count": int(len(work)),
    }
    return work, retained, metadata


def primary_roles(specs: list[MetricSpec]) -> dict[str, str | None]:
    result = {
        "train_cost": None,
        "validation_cost": None,
        "validation_performance": None,
        "train_performance": None,
    }
    for spec in specs:
        if spec.role == "TRAIN_COST" and result["train_cost"] is None:
            result["train_cost"] = spec.column
        elif spec.role == "VALIDATION_COST" and result["validation_cost"] is None:
            result["validation_cost"] = spec.column
        elif spec.role == "VALIDATION_PERFORMANCE" and result["validation_performance"] is None:
            result["validation_performance"] = spec.column
        elif spec.role == "TRAIN_PERFORMANCE" and result["train_performance"] is None:
            result["train_performance"] = spec.column
    return result


def oriented_improvement(
    start: np.ndarray, end: np.ndarray, specs: list[MetricSpec], scales: np.ndarray
) -> np.ndarray:
    delta = end - start
    oriented = np.empty_like(delta, dtype=float)
    for idx, spec in enumerate(specs):
        if spec.direction == "LOWER_IS_BETTER":
            oriented[idx] = -delta[idx] / scales[idx]
        elif spec.direction == "HIGHER_IS_BETTER":
            oriented[idx] = delta[idx] / scales[idx]
        else:
            # Unknown-direction signals are described but not treated as intrinsically good.
            oriented[idx] = delta[idx] / scales[idx]
    return oriented


def derive_threshold(magnitudes: np.ndarray) -> float:
    positive = magnitudes[np.isfinite(magnitudes)]
    if len(positive) == 0:
        return 0.15
    q20 = float(np.quantile(positive, 0.20))
    median = float(np.median(positive))
    return max(0.12, min(0.55, 0.55 * q20 + 0.10 * median))


def get_value(mapping: dict[str, float], key: str | None) -> float | None:
    return None if key is None else float(mapping[key])


def classify_window(
    improvements: dict[str, float],
    raw_start: dict[str, float],
    raw_end: dict[str, float],
    roles: dict[str, str | None],
    activity: float,
    threshold: float,
) -> tuple[str, str]:
    if activity < threshold:
        return "PLATEAU", "LOW_ACTIVITY"

    train_cost = get_value(improvements, roles["train_cost"])
    validation_cost = get_value(improvements, roles["validation_cost"])
    train_perf = get_value(improvements, roles["train_performance"])
    validation_perf = get_value(improvements, roles["validation_performance"])

    positive = threshold / max(math.sqrt(max(len(improvements), 1)), 1.0)
    negative = -positive

    # Full train/validation cost geometry.
    if train_cost is not None and validation_cost is not None:
        train_col = roles["train_cost"]
        val_col = roles["validation_cost"]
        gap_start = abs(raw_start[val_col] - raw_start[train_col])
        gap_end = abs(raw_end[val_col] - raw_end[train_col])
        gap_improvement_raw = gap_start - gap_end
        gap_scale = max(abs(gap_start), abs(gap_end), 1e-9)
        gap_improvement = gap_improvement_raw / gap_scale

        perf_support = validation_perf is None or validation_perf > negative

        if train_cost > positive and validation_cost > positive and perf_support:
            if gap_improvement < -0.08:
                return "FAVORABLE_GAP_WARNING", "TRAIN_AND_VALIDATION_IMPROVE_GAP_WIDENS"
            return "FAVORABLE", "TRAIN_AND_VALIDATION_IMPROVE"
        if train_cost > positive and validation_cost < negative:
            return "OVERFIT_DRIFT", "TRAIN_IMPROVES_VALIDATION_DEGRADES"
        if train_cost < negative and validation_cost < negative:
            return "DEGRADATION", "TRAIN_AND_VALIDATION_DEGRADE"
        return "MIXED", "INCONSISTENT_TRAIN_VALIDATION_GEOMETRY"

    # Train cost with validation performance but no validation cost.
    if train_cost is not None and validation_perf is not None:
        if train_cost > positive and validation_perf > positive:
            return "FAVORABLE", "TRAIN_COST_AND_VALIDATION_PERFORMANCE_IMPROVE"
        if train_cost > positive and validation_perf < negative:
            return "OVERFIT_DRIFT", "TRAIN_IMPROVES_VALIDATION_PERFORMANCE_DEGRADES"
        if train_cost < negative and validation_perf < negative:
            return "DEGRADATION", "TRAIN_AND_VALIDATION_DEGRADE"
        return "MIXED", "INCONSISTENT_TRAIN_VALIDATION_GEOMETRY"

    # Train-only learning.
    if train_cost is not None:
        if train_cost > positive:
            return "IMPROVING_TRAIN_ONLY", "TRAIN_COST_IMPROVES_REFERENCE_LIMITED"
        if train_cost < negative:
            return "WORSENING_TRAIN_ONLY", "TRAIN_COST_DEGRADES_REFERENCE_LIMITED"
        return "PLATEAU", "TRAIN_ONLY_LOW_NET_PROGRESS"

    if train_perf is not None:
        if train_perf > positive:
            return "IMPROVING_TRAIN_ONLY", "TRAIN_PERFORMANCE_IMPROVES_REFERENCE_LIMITED"
        if train_perf < negative:
            return "WORSENING_TRAIN_ONLY", "TRAIN_PERFORMANCE_DEGRADES_REFERENCE_LIMITED"
        return "PLATEAU", "TRAIN_ONLY_LOW_NET_PROGRESS"

    # Validation-only or generic multimetric fallback.
    known_values = [
        value
        for key, value in improvements.items()
        if np.isfinite(value)
    ]
    positive_rate = float(np.mean(np.array(known_values) > positive))
    negative_rate = float(np.mean(np.array(known_values) < negative))

    if validation_cost is not None or validation_perf is not None:
        validation_value = (
            validation_cost if validation_cost is not None else validation_perf
        )
        if validation_value > positive:
            return "VALIDATION_IMPROVING", "VALIDATION_ONLY_IMPROVEMENT"
        if validation_value < negative:
            return "VALIDATION_DEGRADING", "VALIDATION_ONLY_DEGRADATION"

    if positive_rate >= 0.67:
        return "MULTIMETRIC_IMPROVING", "GENERIC_MULTIMETRIC_IMPROVEMENT"
    if negative_rate >= 0.67:
        return "MULTIMETRIC_DEGRADING", "GENERIC_MULTIMETRIC_DEGRADATION"
    return "UNKNOWN_NOVEL", "NO_FROZEN_GRAMMAR_MATCH"


def entropy(labels: list[str]) -> float:
    if not labels:
        return 0.0
    _, counts = np.unique(np.asarray(labels, dtype=object), return_counts=True)
    probabilities = counts / counts.sum()
    return float(-(probabilities * np.log2(probabilities)).sum())


def distribution(labels: list[str]) -> dict[str, float]:
    if not labels:
        return {}
    values, counts = np.unique(np.asarray(labels, dtype=object), return_counts=True)
    total = counts.sum()
    return {str(v): float(c / total) for v, c in zip(values, counts)}


def smooth_isolated_labels(labels: list[str]) -> list[str]:
    smoothed = labels.copy()
    for idx in range(1, len(labels) - 1):
        if labels[idx - 1] == labels[idx + 1] != labels[idx]:
            smoothed[idx] = labels[idx - 1]
    return smoothed


def run_lengths(labels: list[str]) -> list[dict[str, Any]]:
    if not labels:
        return []
    output = []
    start = 0
    current = labels[0]
    for idx in range(1, len(labels)):
        if labels[idx] != current:
            output.append(
                {"label": current, "start": start, "end": idx - 1, "length": idx - start}
            )
            start = idx
            current = labels[idx]
    output.append(
        {"label": current, "start": start, "end": len(labels) - 1, "length": len(labels) - start}
    )
    return output


def phase_metrics(records: list[dict[str, Any]]) -> dict[str, Any]:
    micro = [record["micro_code"] for record in records]
    morph = [record["morphology"] for record in records]
    h_micro = entropy(micro)
    h_morph = entropy(morph)
    hidden = 0.0 if h_micro <= 1e-12 else float(
        np.clip(1.0 - h_morph / h_micro, 0.0, 1.0)
    )

    dist = distribution(morph)
    ordered = sorted(dist.items(), key=lambda item: item[1], reverse=True)
    dominant = ordered[0][0] if ordered else ""
    rate = ordered[0][1] if ordered else 0.0
    runner_up = ordered[1][1] if len(ordered) > 1 else 0.0

    smoothed = smooth_isolated_labels(morph)
    runs = run_lengths(smoothed)
    longest_run_fraction = (
        max(run["length"] for run in runs) / len(smoothed) if smoothed else 0.0
    )
    adjacent_persistence = (
        float(np.mean(np.asarray(smoothed[1:]) == np.asarray(smoothed[:-1])))
        if len(smoothed) > 1 else 1.0
    )

    confidence = float(np.clip(
        0.45 * rate
        + 0.25 * (rate - runner_up)
        + 0.15 * longest_run_fraction
        + 0.15 * adjacent_persistence,
        0.0,
        1.0,
    ))

    if hidden >= 0.80:
        lock = "STRONG_LOCK"
    elif hidden >= 0.55:
        lock = "MODERATE_LOCK"
    elif hidden >= 0.30:
        lock = "WEAK_LOCK"
    else:
        lock = "OPEN_OR_DIVERSE"

    return {
        "n_windows": len(records),
        "Hmicro": h_micro,
        "Hmorph": h_morph,
        "Dhidden": hidden,
        "dominant_morphology": dominant,
        "dominant_rate": rate,
        "runner_up_rate": runner_up,
        "dominance_margin": rate - runner_up,
        "confidence": confidence,
        "lock_status": lock,
        "adjacent_persistence": adjacent_persistence,
        "longest_run_fraction": longest_run_fraction,
        "distribution": dist,
    }


def total_variation(first: dict[str, float], second: dict[str, float]) -> float:
    keys = set(first) | set(second)
    return float(0.5 * sum(abs(first.get(key, 0.0) - second.get(key, 0.0)) for key in keys))


def chronology_score(records: list[dict[str, Any]]) -> dict[str, float]:
    labels = smooth_isolated_labels([record["morphology"] for record in records])
    midpoint = len(records) // 2
    early_records = records[:midpoint]
    late_records = records[midpoint:]
    early = phase_metrics(early_records)
    late = phase_metrics(late_records)

    runs = run_lengths(labels)
    longest = max((run["length"] for run in runs), default=0) / max(len(labels), 1)
    tvd = total_variation(early["distribution"], late["distribution"])
    hidden_shift = abs(late["Dhidden"] - early["Dhidden"])

    score = float(np.clip(
        0.50 * tvd + 0.30 * longest + 0.20 * hidden_shift,
        0.0,
        1.0,
    ))
    return {
        "score": score,
        "phase_tvd": tvd,
        "longest_run_fraction": longest,
        "hidden_shift": hidden_shift,
    }


def calibrate_windows(
    matrix: pd.DataFrame, specs: list[MetricSpec], window: int
) -> dict[str, Any]:
    values = matrix.to_numpy(dtype=float)
    centers = []
    scales = []
    for idx in range(values.shape[1]):
        center, scale = robust_center_scale(values[:, idx])
        centers.append(center)
        scales.append(scale)
    centers_array = np.asarray(centers)
    scales_array = np.asarray(scales)

    provisional = []
    for start in range(len(values) - window + 1):
        segment = values[start : start + window]
        improvement = oriented_improvement(
            segment[0], segment[-1], specs, scales_array
        )
        magnitude = float(np.linalg.norm(improvement))
        provisional.append(magnitude)

    magnitudes = np.asarray(provisional, dtype=float)
    quartiles = np.quantile(magnitudes, [0.25, 0.50, 0.75])
    threshold = derive_threshold(magnitudes)
    return {
        "centers": centers_array,
        "scales": scales_array,
        "magnitude_quartiles": quartiles,
        "activity_threshold": threshold,
    }


def build_windows(
    matrix: pd.DataFrame,
    specs: list[MetricSpec],
    window: int,
    calibration: dict[str, Any],
) -> list[dict[str, Any]]:
    values = matrix.to_numpy(dtype=float)
    columns = list(matrix.columns)
    roles = primary_roles(specs)
    scales = calibration["scales"]
    quartiles = calibration["magnitude_quartiles"]
    threshold = calibration["activity_threshold"]

    records = []
    for start in range(len(values) - window + 1):
        segment = values[start : start + window]
        raw_start = {column: float(segment[0, idx]) for idx, column in enumerate(columns)}
        raw_end = {column: float(segment[-1, idx]) for idx, column in enumerate(columns)}
        improvement_vector = oriented_improvement(
            segment[0], segment[-1], specs, scales
        )
        improvements = {
            column: float(improvement_vector[idx])
            for idx, column in enumerate(columns)
        }
        magnitude = float(np.linalg.norm(improvement_vector))

        standardized = (segment - calibration["centers"]) / scales
        path = np.diff(standardized, axis=0)
        path_length = float(np.linalg.norm(path, axis=1).sum())
        net_length = float(np.linalg.norm(standardized[-1] - standardized[0]))
        roughness = path_length / (net_length + 1e-9)

        morphology, reason = classify_window(
            improvements, raw_start, raw_end, roles, magnitude, threshold
        )
        magnitude_bin = int(np.searchsorted(quartiles, magnitude, side="right"))
        roughness_bin = 0 if roughness < 1.10 else 1 if roughness < 1.60 else 2
        direction = improvement_vector / (magnitude + 1e-9)
        direction_bin = tuple(
            np.clip(np.round(direction * 2), -2, 2).astype(int).tolist()
        )
        micro_code = str((morphology, magnitude_bin, roughness_bin, direction_bin))

        records.append(
            {
                "window_index": len(records),
                "start_row": start,
                "end_row": start + window - 1,
                "morphology": morphology,
                "reason": reason,
                "magnitude": magnitude,
                "roughness": roughness,
                "magnitude_bin": magnitude_bin,
                "roughness_bin": roughness_bin,
                "direction_bin": direction_bin,
                "micro_code": micro_code,
                "improvements": improvements,
            }
        )
    return records


def segment_records(records: list[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    n = len(records)
    one_third = n // 3
    two_thirds = 2 * n // 3
    midpoint = n // 2
    return {
        "GLOBAL": records,
        "EARLY": records[:midpoint],
        "LATE": records[midpoint:],
        "EARLY_THIRD": records[:one_third],
        "MIDDLE_THIRD": records[one_third:two_thirds],
        "LATE_THIRD": records[two_thirds:],
    }


def reconstruct_from_permuted_increments(
    matrix: pd.DataFrame, order: np.ndarray
) -> pd.DataFrame:
    values = matrix.to_numpy(dtype=float)
    increments = np.diff(values, axis=0)
    reconstructed = np.vstack(
        [values[0], values[0] + np.cumsum(increments[order], axis=0)]
    )
    return pd.DataFrame(reconstructed, columns=matrix.columns)


def analyze_file(
    path: Path,
    out_root: Path,
    requested_window: int | None,
    n_surrogates: int,
    seed: int,
    min_validation_coverage: float,
    make_plots: bool,
) -> dict[str, Any]:
    name = path.stem
    safe_name = normalize_label(name)
    outdir = out_root / safe_name
    outdir.mkdir(parents=True, exist_ok=True)

    df = pd.read_csv(path)
    specs, time_column, excluded = infer_metric_specs(df)
    matrix, retained, prep_meta = prepare_matrix(
        df, specs, min_validation_coverage=min_validation_coverage
    )

    if len(retained) == 0:
        raise ValueError(f"No usable metrics detected in {path.name}.")
    if len(matrix) < 8:
        raise ValueError(f"Too few usable rows in {path.name}: {len(matrix)}.")

    window = choose_window_length(len(matrix), requested_window)
    calibration = calibrate_windows(matrix, retained, window)
    records = build_windows(matrix, retained, window, calibration)

    phases = {
        phase: phase_metrics(values)
        for phase, values in segment_records(records).items()
        if values
    }
    chronological = chronology_score(records)

    rng = np.random.default_rng(seed)
    increments_count = len(matrix) - 1
    surrogate_scores = np.empty(n_surrogates, dtype=float)
    surrogate_tvd = np.empty(n_surrogates, dtype=float)

    for idx in range(n_surrogates):
        order = rng.permutation(increments_count)
        surrogate_matrix = reconstruct_from_permuted_increments(matrix, order)
        surrogate_records = build_windows(
            surrogate_matrix, retained, window, calibration
        )
        surrogate_chronology = chronology_score(surrogate_records)
        surrogate_scores[idx] = surrogate_chronology["score"]
        surrogate_tvd[idx] = surrogate_chronology["phase_tvd"]

    p_chronology = float(
        (1 + np.sum(surrogate_scores >= chronological["score"]))
        / (n_surrogates + 1)
    )

    reverse_matrix = matrix.iloc[::-1].reset_index(drop=True)
    reverse_records = build_windows(reverse_matrix, retained, window, calibration)
    reverse_chronology = chronology_score(reverse_records)

    labels = smooth_isolated_labels([record["morphology"] for record in records])
    transitions = []
    for run_index, run in enumerate(run_lengths(labels)):
        transitions.append(
            {
                "run_index": run_index,
                "morphology": run["label"],
                "start_window": run["start"],
                "end_window": run["end"],
                "length": run["length"],
                "fraction_of_run": run["length"] / len(labels),
            }
        )

    validation_available = any(
        spec.role.startswith("VALIDATION") for spec in retained
    )
    reference_quality = (
        "TRAIN_AND_VALIDATION"
        if validation_available
        else "REFERENCE_LIMITED_TRAIN_ONLY"
    )

    global_state = phases["GLOBAL"]
    current_state = phases["LATE"]
    terminal_run = transitions[-1] if transitions else {
        "morphology": current_state["dominant_morphology"],
        "length": 0,
        "fraction_of_run": 0.0,
    }

    if current_state["confidence"] >= 0.75:
        confidence_label = "HIGH"
    elif current_state["confidence"] >= 0.55:
        confidence_label = "MODERATE"
    else:
        confidence_label = "LOW"

    current_label = current_state["dominant_morphology"]
    if current_label in ("OVERFIT_DRIFT", "DEGRADATION", "VALIDATION_DEGRADING"):
        alert_level = "RED"
    elif current_label in (
        "PLATEAU", "MIXED", "UNKNOWN_NOVEL",
        "WORSENING_TRAIN_ONLY", "MULTIMETRIC_DEGRADING"
    ):
        alert_level = "ORANGE"
    elif current_label == "FAVORABLE_GAP_WARNING":
        alert_level = "YELLOW"
    elif current_label in (
        "FAVORABLE", "IMPROVING_TRAIN_ONLY",
        "VALIDATION_IMPROVING", "MULTIMETRIC_IMPROVING"
    ):
        alert_level = "GREEN"
    else:
        alert_level = "ORANGE"

    result = {
        "version": VERSION,
        "input_file": path.name,
        "input_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "rows": int(len(df)),
        "usable_rows": int(len(matrix)),
        "window_length": window,
        "n_windows": len(records),
        "time_column": time_column,
        "excluded_columns": excluded,
        "metric_specs": [asdict(spec) for spec in retained],
        "preparation": prep_meta,
        "reference_quality": reference_quality,
        "automatic_calibration": {
            "activity_threshold": float(calibration["activity_threshold"]),
            "magnitude_quartiles": [
                float(value) for value in calibration["magnitude_quartiles"]
            ],
        },
        "dominant_morphology": current_state["dominant_morphology"],
        "dominant_rate": current_state["dominant_rate"],
        "dominant_confidence": current_state["confidence"],
        "confidence_label": confidence_label,
        "alert_level": alert_level,
        "lock_status": current_state["lock_status"],
        "Hmicro": current_state["Hmicro"],
        "Hmorph": current_state["Hmorph"],
        "Dhidden": current_state["Dhidden"],
        "current_state_basis": "LATE_HALF",
        "terminal_run_morphology": terminal_run["morphology"],
        "terminal_run_length": terminal_run["length"],
        "terminal_run_fraction": terminal_run["fraction_of_run"],
        "global_dominant_morphology": global_state["dominant_morphology"],
        "global_dominant_rate": global_state["dominant_rate"],
        "global_confidence": global_state["confidence"],
        "global_lock_status": global_state["lock_status"],
        "global_Hmicro": global_state["Hmicro"],
        "global_Hmorph": global_state["Hmorph"],
        "global_Dhidden": global_state["Dhidden"],
        "phases": phases,
        "transitions": transitions,
        "chronology": {
            **chronological,
            "surrogate_count": n_surrogates,
            "surrogate_score_mean": float(np.mean(surrogate_scores)),
            "surrogate_score_std": float(np.std(surrogate_scores)),
            "p_chronology": p_chronology,
            "reverse_score": reverse_chronology["score"],
            "reverse_phase_tvd": reverse_chronology["phase_tvd"],
        },
    }

    # Window CSV.
    window_rows = []
    for record in records:
        row = {
            key: value
            for key, value in record.items()
            if key not in ("improvements", "direction_bin", "micro_code")
        }
        row["direction_bin"] = str(record["direction_bin"])
        row["micro_code"] = record["micro_code"]
        for metric, value in record["improvements"].items():
            row[f"improvement__{metric}"] = value
        window_rows.append(row)
    pd.DataFrame(window_rows).to_csv(
        outdir / "windows.csv", index=False
    )
    pd.DataFrame(transitions).to_csv(
        outdir / "transitions.csv", index=False
    )
    pd.DataFrame(
        [
            {
                "phase": phase,
                **{
                    key: value
                    for key, value in metrics.items()
                    if key != "distribution"
                },
                "distribution_json": json.dumps(
                    metrics["distribution"], sort_keys=True
                ),
            }
            for phase, metrics in phases.items()
        ]
    ).to_csv(outdir / "phase_summary.csv", index=False)

    (outdir / "summary.json").write_text(
        json.dumps(result, ensure_ascii=False, indent=2), encoding="utf-8"
    )

    if make_plots and plt is not None:
        unique_labels = sorted(set(labels))
        mapping = {label: idx for idx, label in enumerate(unique_labels)}
        y = [mapping[label] for label in labels]
        plt.figure(figsize=(10, 4.8))
        plt.plot(range(len(y)), y, marker="o")
        plt.yticks(range(len(unique_labels)), unique_labels)
        plt.xlabel("Fenêtre chronologique")
        plt.ylabel("Morphologie automatique")
        plt.title(f"INSACERMO V28 — {path.name}")
        plt.tight_layout()
        plt.savefig(outdir / "morphology_timeline.png", dpi=180)
        plt.close()

        phase_names = ["EARLY", "MIDDLE_THIRD", "LATE"]
        available = [phase for phase in phase_names if phase in phases]
        plt.figure(figsize=(8.5, 4.8))
        plt.bar(
            available,
            [phases[phase]["Dhidden"] for phase in available],
        )
        plt.ylim(0, 1.05)
        plt.ylabel("Fermeture cachée")
        plt.title(f"INSACERMO V28 — verrouillage morphologique : {path.name}")
        plt.tight_layout()
        plt.savefig(outdir / "hidden_closure_phases.png", dpi=180)
        plt.close()

    return result


def write_batch_summary(results: list[dict[str, Any]], out_root: Path) -> None:
    rows = []
    for result in results:
        early = result["phases"].get("EARLY", {})
        late = result["phases"].get("LATE", {})
        rows.append(
            {
                "input_file": result["input_file"],
                "reference_quality": result["reference_quality"],
                "dominant_morphology": result["dominant_morphology"],
                "dominant_rate": result["dominant_rate"],
                "dominant_confidence": result["dominant_confidence"],
                "confidence_label": result["confidence_label"],
                "alert_level": result["alert_level"],
                "lock_status": result["lock_status"],
                "Hmicro": result["Hmicro"],
                "Hmorph": result["Hmorph"],
                "Dhidden": result["Dhidden"],
                "global_dominant": result["global_dominant_morphology"],
                "global_Dhidden": result["global_Dhidden"],
                "early_dominant": early.get("dominant_morphology", ""),
                "early_Dhidden": early.get("Dhidden", np.nan),
                "late_dominant": late.get("dominant_morphology", ""),
                "late_Dhidden": late.get("Dhidden", np.nan),
                "terminal_run": result["terminal_run_morphology"],
                "transition_count": max(len(result["transitions"]) - 1, 0),
                "chronology_score": result["chronology"]["score"],
                "p_chronology": result["chronology"]["p_chronology"],
            }
        )
    frame = pd.DataFrame(rows)
    frame.to_csv(out_root / "batch_summary.csv", index=False)

    if plt is not None and len(frame):
        positions = np.arange(len(frame))
        plt.figure(figsize=(10, 5.2))
        plt.bar(positions, frame["Dhidden"])
        plt.xticks(positions, frame["input_file"], rotation=20, ha="right")
        plt.ylim(0, 1.05)
        plt.ylabel("Fermeture cachée globale")
        plt.title("INSACERMO V28 — audit automatique du batch")
        plt.tight_layout()
        plt.savefig(out_root / "batch_hidden_closure.png", dpi=180)
        plt.close()


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Automatic INSACERMO dominant-morphology detector for CSV logs."
    )
    parser.add_argument("files", nargs="+", help="One or more CSV files.")
    parser.add_argument("--out", default="insacermo_v28_results")
    parser.add_argument("--window", type=int, default=None)
    parser.add_argument("--surrogates", type=int, default=199)
    parser.add_argument("--seed", type=int, default=DEFAULT_SEED)
    parser.add_argument("--min-validation-coverage", type=float, default=0.25)
    parser.add_argument("--no-plots", action="store_true")
    args = parser.parse_args()

    out_root = Path(args.out)
    out_root.mkdir(parents=True, exist_ok=True)

    results = []
    failures = []
    for filename in args.files:
        path = Path(filename)
        try:
            result = analyze_file(
                path=path,
                out_root=out_root,
                requested_window=args.window,
                n_surrogates=args.surrogates,
                seed=args.seed,
                min_validation_coverage=args.min_validation_coverage,
                make_plots=not args.no_plots,
            )
            results.append(result)
            print(
                f"{path.name}: {result['dominant_morphology']} "
                f"(rate={result['dominant_rate']:.3f}, "
                f"confidence={result['dominant_confidence']:.3f}, "
                f"Dhidden={result['Dhidden']:.3f}, "
                f"p_chronology={result['chronology']['p_chronology']:.4f})"
            )
        except Exception as exc:
            failures.append({"file": filename, "error": str(exc)})
            print(f"{path.name}: ERROR — {exc}")

    write_batch_summary(results, out_root)
    manifest = {
        "version": VERSION,
        "results": results,
        "failures": failures,
    }
    (out_root / "batch_manifest.json").write_text(
        json.dumps(manifest, ensure_ascii=False, indent=2), encoding="utf-8"
    )
    return 0 if results and not failures else 1


if __name__ == "__main__":
    raise SystemExit(main())
