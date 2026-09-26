"""Minimal HTTP API and static-site server for INSACERMO Engine V1.

No external web framework is required.

Endpoints
---------
GET  /api/health
GET  /api/backends
POST /api/analyze
GET  /...              static files from site_prototype/

Run:
    python -m engine.http_api_v1 --host 127.0.0.1 --port 8000

Then open:
    http://127.0.0.1:8000/
"""

from __future__ import annotations

import argparse
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
import json
from pathlib import Path
from typing import Any

from engine.contract_cli_v1 import run_payload


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SITE_DIR = ROOT / "site_prototype"
MAX_BODY_BYTES = 1_000_000

BACKENDS = [
    {
        "type": "exact_catalogue",
        "label": "Catalogue fini exact",
        "evidence": "exact relative to supplied finite model",
    },
    {
        "type": "rhea_resource_frozen",
        "label": "Rhea — ressource locale",
        "evidence": "exact frozen finite-inventory witness",
    },
    {
        "type": "pglib_ieee14_dc_frozen",
        "label": "PGLib IEEE-14 — DC exact",
        "evidence": "exact frozen Farkas/extreme-ray certificate slice",
    },
    {
        "type": "modechoice14_frozen",
        "label": "ModeChoice — structure réelle 14 mondes",
        "evidence": "exact finite structural audit on frozen real-data-derived sample",
    },
]


def _json_bytes(value: Any) -> bytes:
    return json.dumps(value, ensure_ascii=False, indent=2).encode("utf-8")


class InsacermoHandler(SimpleHTTPRequestHandler):
    server_version = "INSACERMO-HTTP/1.0"

    def __init__(self, *args, directory: str | None = None, **kwargs):
        super().__init__(
            *args,
            directory=directory or str(DEFAULT_SITE_DIR),
            **kwargs,
        )

    def _send_json(self, status: int, value: Any) -> None:
        data = _json_bytes(value)
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(data)

    def _read_json(self) -> dict:
        raw_length = self.headers.get("Content-Length")
        if raw_length is None:
            raise ValueError("missing Content-Length")
        try:
            length = int(raw_length)
        except ValueError as exc:
            raise ValueError("invalid Content-Length") from exc
        if length < 0 or length > MAX_BODY_BYTES:
            raise ValueError("request body too large")
        raw = self.rfile.read(length)
        try:
            value = json.loads(raw.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise ValueError("request body must be valid UTF-8 JSON") from exc
        if not isinstance(value, dict):
            raise ValueError("request JSON must be an object")
        return value

    def do_GET(self) -> None:  # noqa: N802
        if self.path.split("?", 1)[0] == "/api/health":
            self._send_json(
                200,
                {
                    "ok": True,
                    "service": "insacermo-contract-engine",
                    "api_version": "v1",
                    "backends": [b["type"] for b in BACKENDS],
                },
            )
            return

        if self.path.split("?", 1)[0] == "/api/backends":
            self._send_json(200, {"backends": BACKENDS})
            return

        super().do_GET()

    def do_POST(self) -> None:  # noqa: N802
        path = self.path.split("?", 1)[0]
        if path != "/api/analyze":
            self._send_json(404, {"error": "unknown API endpoint"})
            return

        try:
            payload = self._read_json()
            result = run_payload(payload)
        except (KeyError, TypeError, ValueError) as exc:
            self._send_json(400, {"error": str(exc)})
            return
        except Exception as exc:  # conservative API boundary
            self._send_json(
                500,
                {
                    "error": "engine execution failed",
                    "detail": str(exc),
                },
            )
            return

        self._send_json(200, result)

    def log_message(self, fmt: str, *args: object) -> None:
        # Keep the standard server useful from a terminal without noisy DNS data.
        print(f"[INSACERMO] {self.address_string()} - {fmt % args}")


def make_server(
    host: str = "127.0.0.1",
    port: int = 8000,
    site_dir: Path | str = DEFAULT_SITE_DIR,
) -> ThreadingHTTPServer:
    directory = str(Path(site_dir).resolve())

    class BoundHandler(InsacermoHandler):
        def __init__(self, *args, **kwargs):
            super().__init__(*args, directory=directory, **kwargs)

    return ThreadingHTTPServer((host, port), BoundHandler)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Serve the INSACERMO site and contract API."
    )
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", default=8000, type=int)
    parser.add_argument("--site-dir", type=Path, default=DEFAULT_SITE_DIR)
    args = parser.parse_args(argv)

    httpd = make_server(args.host, args.port, args.site_dir)
    actual_host, actual_port = httpd.server_address[:2]
    print(f"INSACERMO_HTTP_API_V1 READY http://{actual_host}:{actual_port}/")
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        httpd.server_close()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
