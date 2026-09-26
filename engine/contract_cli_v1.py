"""JSON CLI for the INSACERMO Contract Engine V1.

Usage:
  python -m engine.contract_cli_v1 input.json
  python -m engine.contract_cli_v1 input.json --pretty

Input shape:
{
  "contract": {...},
  "backend": {
    "type": "exact_catalogue",
    ...
  }
}
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from engine.contract_io_v1 import (
    ContractInput,
    FutureRequirement,
    evaluate_contract,
)
from engine.exact_catalogue_backend_v1 import (
    audit_exact_catalogue,
    model_from_dict,
)
from engine.rhea_resource_backend_v1 import (
    FrozenRheaResourceModel,
    audit_frozen_rhea_resource,
)


def contract_from_dict(data: dict) -> ContractInput:
    return ContractInput(
        contract_id=data.get("contract_id", "default"),
        horizon=data.get("horizon"),
        requirements=[
            FutureRequirement(
                future_id=r["future_id"],
                required=r.get("required", True),
                weight=float(r.get("weight", 1.0)),
                deadline=r.get("deadline"),
                description=r.get("description", ""),
            )
            for r in data.get("requirements", [])
        ],
    )


def run_payload(payload: dict) -> dict:
    contract = contract_from_dict(payload["contract"])
    backend = payload["backend"]
    backend_type = backend.get("type")

    if backend_type == "exact_catalogue":
        model = model_from_dict(backend)
        audit = audit_exact_catalogue(contract, model)
    elif backend_type == "rhea_resource_frozen":
        model = FrozenRheaResourceModel(
            model_id=backend.get(
                "model_id", "rhea-frozen-naringenin-resource-v1"
            ),
            repair_cost=float(backend.get("repair_cost", 1.0)),
        )
        audit = audit_frozen_rhea_resource(contract, model)
    else:
        raise ValueError(
            f"unsupported backend type {backend_type!r}; currently supported: "
            "exact_catalogue, rhea_resource_frozen"
        )
    return evaluate_contract(contract, audit).to_dict()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Run the INSACERMO contract engine on one JSON payload."
    )
    parser.add_argument("input", type=Path)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    try:
        payload = json.loads(args.input.read_text(encoding="utf-8"))
        result = run_payload(payload)
    except Exception as exc:
        print(json.dumps({"error": str(exc)}, ensure_ascii=False), file=sys.stderr)
        return 2

    print(
        json.dumps(
            result,
            ensure_ascii=False,
            indent=2 if args.pretty else None,
            sort_keys=args.pretty,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
