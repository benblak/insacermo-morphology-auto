from __future__ import annotations

import json
from pathlib import Path
import threading
from urllib.error import HTTPError
from urllib.request import Request, urlopen

from engine.http_api_v1 import make_server


ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / "site_prototype"


def request_json(url: str, payload=None):
    data = None
    headers = {}
    if payload is not None:
        data = json.dumps(payload).encode("utf-8")
        headers["Content-Type"] = "application/json"
    req = Request(url, data=data, headers=headers)
    with urlopen(req, timeout=5) as response:
        return response.status, json.loads(response.read().decode("utf-8"))


def load(name: str):
    return json.loads((SITE / name).read_text(encoding="utf-8"))


def main():
    server = make_server("127.0.0.1", 0, SITE)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    host, port = server.server_address[:2]
    base = f"http://{host}:{port}"

    try:
        status, health = request_json(base + "/api/health")
        assert status == 200
        assert health["ok"] is True
        assert len(health["backends"]) == 4

        cases = [
            ("contract_input_example.json", "REPAIR"),
            ("rhea_contract_input_example.json", "REPAIR"),
            ("pglib_contract_input_example.json", "REPAIR"),
            ("modechoice_contract_input_example.json", "REPAIR"),
        ]
        for filename, expected in cases:
            status, result = request_json(
                base + "/api/analyze",
                load(filename),
            )
            assert status == 200, (filename, result)
            assert result["decision"] == expected, (filename, result)

        bad = {
            "contract": {
                "contract_id": "bad",
                "requirements": [{"future_id": "X"}],
            },
            "backend": {"type": "does_not_exist"},
        }
        try:
            request_json(base + "/api/analyze", bad)
            raise AssertionError("invalid backend should return HTTP 400")
        except HTTPError as exc:
            assert exc.code == 400
            body = json.loads(exc.read().decode("utf-8"))
            assert "unsupported backend type" in body["error"]

        with urlopen(base + "/", timeout=5) as response:
            page = response.read().decode("utf-8")
            assert "INSACERMO" in page
            assert "/api/analyze" in page

        print("HTTP_API_V1_TESTS: PASS (health + 4 engine calls + error + site)")
    finally:
        server.shutdown()
        server.server_close()
        thread.join(timeout=5)


if __name__ == "__main__":
    main()
