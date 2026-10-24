#!/usr/bin/env python3
"""Recompute the rigorous arithmetic certificate; height theory is in the README.
Python's machine/version string is the only ignored reproduction field.
"""
from pathlib import Path
import json
import os
import subprocess
import sys
import tempfile

if sys.flags.optimize or os.environ.get("PYTHONOPTIMIZE") not in (None, "", "0"):
    raise SystemExit("Certificate assertions must be enabled; do not use Python optimization.")

root = Path(__file__).resolve().parents[1]
source = root / "cas/height-bounds"
with tempfile.TemporaryDirectory(prefix="erdos677-height-") as directory:
    result = Path(directory) / "replayed.json"
    subprocess.run([sys.executable, str(source / "certify_height_intervals.py"),
                    str(source / "duplication_bounds.json"),
                    "--iterations", "7", "--lambda-lower", "1/100",
                    "--output", str(result)], check=True)
    expected = json.loads((source / "height_intervals.json").read_text())
    actual = json.loads(result.read_text())
    for record in (expected, actual):
        record.pop("python_version")
    if expected != actual:
        raise SystemExit("FAIL: recomputed mathematical certificate differs from saved output")
print("PASS: four exact height certificates; S=5, lambda=1/100; all mathematical fields match.")
