"""Explicit generation or read-only comparison for descent certificates."""
import argparse
import hashlib
import json

def finish(path, data):
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true", help="intentionally regenerate the stored certificate")
    args = parser.parse_args()
    if args.write:
        path.write_text(json.dumps(data, default=str, indent=2) + "\n")
    else:
        # Normalize Fraction/tuple values to the JSON representation.
        expected = json.loads(json.dumps(data, default=str))
        if json.loads(path.read_text()) != expected:
            raise AssertionError(f"Stored certificate differs from exact replay: {path.name}")
    return hashlib.sha256(path.read_bytes()).hexdigest()
