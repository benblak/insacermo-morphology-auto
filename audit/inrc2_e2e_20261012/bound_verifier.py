#!/usr/bin/env python3
"""External expected-contract-binding gate for frozen INSACERMO C3.

Expected digest must be supplied by the trusted caller, separately from
the receipt directory. This tool makes no claim of authenticating that caller.
"""
import argparse
import hashlib
import hmac
import json
import re
import sys
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from insacermo_one_engine import canonical, replay

HEX256=re.compile(r"[0-9a-f]{64}\Z")

def verify_bound(folder, expected_sha256, *, lean_binary="lean"):
    if not isinstance(expected_sha256,str) or HEX256.fullmatch(expected_sha256) is None:
        return False
    folder=Path(folder)
    try:
        raw=(folder/"contract.json").read_bytes()
        model=json.loads(raw)
        actual=hashlib.sha256(canonical(model)).hexdigest()
    except (OSError,ValueError,TypeError,UnicodeError,RecursionError):
        return False
    if not hmac.compare_digest(actual,expected_sha256):
        return False
    return bool(replay(folder,lean_binary=lean_binary))

def main(argv=None):
    p=argparse.ArgumentParser(description="Verify original C3 receipt only for the independently expected contract hash")
    p.add_argument("receipt_folder",type=Path)
    src=p.add_mutually_exclusive_group(required=True)
    src.add_argument("--expected-contract-sha256")
    src.add_argument("--expected-contract-file",type=Path,
        help="Trusted caller's own contract JSON outside the receipt folder")
    p.add_argument("--lean",default="lean")
    x=p.parse_args(argv)
    if x.expected_contract_file is not None:
        try:
            expected=hashlib.sha256(canonical(json.loads(x.expected_contract_file.read_bytes()))).hexdigest()
        except (OSError,ValueError,TypeError,UnicodeError,RecursionError):
            print("CERTIFICATE_REJECTED");return 2
    else:
        expected=x.expected_contract_sha256
    ok=verify_bound(x.receipt_folder,expected,lean_binary=x.lean)
    print("BOUND_CERTIFICATE_ACCEPTED" if ok else "CERTIFICATE_REJECTED")
    return 0 if ok else 2

if __name__=="__main__":raise SystemExit(main())
