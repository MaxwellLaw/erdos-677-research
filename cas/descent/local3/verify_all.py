#!/usr/bin/env python3
"""Reproduce and compare both exact local-3 certificates without modifying inputs."""
from pathlib import Path
import json
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent

def run(args):
    result = subprocess.run([sys.executable, *map(str, args)], text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)

def main():
    if not __debug__:
        raise RuntimeError("Assertions must remain enabled.")
    expected = json.loads((HERE / "local3_candidates.json").read_text())
    independent = json.loads((HERE / "independent_local3.json").read_text())
    with tempfile.TemporaryDirectory(prefix="erdos677-local3-") as raw:
        temp = Path(raw)
        generator = temp / "certify_local3.py"
        shutil.copyfile(HERE / generator.name, generator)
        run([generator])
        generated = temp / "local3_candidates.json"
        assert json.loads(generated.read_text()) == expected, "candidate certificate differs"
        replay = temp / "independent_local3.json"
        run([HERE / "verify_local3_independent.py", generated, "--output", replay])
        assert json.loads(replay.read_text()) == independent, "independent certificate differs"
    print("PASS: reproduced four global S-supported norm-square witnesses and independent local-3 rank four.")

if __name__ == "__main__":
    main()
