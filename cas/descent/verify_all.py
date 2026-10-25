#!/usr/bin/env python3
"""Replay every stored descent certificate without external CAS or network."""
from pathlib import Path
import subprocess
import sys

HERE=Path(__file__).resolve().parent
STEPS=[
    'verify_export_algebra.py',
    'verify_unit_squareclasses.py',
    'verify_class_relations.py',
    'verify_rank_support.py',
    'local3/verify_all.py',
    'audit_class_lattices.py',
]

def main():
    if not __debug__:
        raise SystemExit('Keep Python assertions enabled.')
    if len(sys.argv)!=1:
        raise SystemExit('Usage: python3 cas/descent/verify_all.py')
    for step in STEPS:
        subprocess.run([sys.executable,str(HERE/step)],check=True,cwd=HERE)
    print('PASS: independent maximal-order, class-relation, Kummer-support, and local-3 arithmetic; all saved certificates match.')

if __name__=='__main__':main()
