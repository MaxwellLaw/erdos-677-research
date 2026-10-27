#!/usr/bin/env python3
"""Run the explicit theorem audit and reject dependencies outside Lean's standard axioms."""
from pathlib import Path
import re
import subprocess
import sys

expected = re.findall(r'^#print axioms (\S+)', Path('Audit.lean').read_text(), re.M)
if not expected or len(expected) != len(set(expected)):
    raise SystemExit('Audit.lean must name distinct explicit declarations')
result = subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', 'Audit.lean'],
                        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
print(result.stdout, end='')
if result.returncode:
    raise SystemExit(result.returncode)
reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout)
reports += [(name, '') for name in re.findall(r"'([^']+)' does not depend on any axioms", result.stdout)]
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
actual = {}
for name, items in reports:
    if name in actual:
        raise SystemExit(f'duplicate report: {name}')
    deps = {x.strip() for x in items.split(',') if x.strip()}
    actual[name] = deps
    if deps - allowed:
        raise SystemExit(f'nonstandard axiom dependency for {name}: {sorted(deps - allowed)}')
if set(actual) != set(expected):
    raise SystemExit(f'report mismatch: missing={set(expected)-set(actual)}, extra={set(actual)-set(expected)}')
print(f'PASS: {len(expected)} explicit declarations; only standard Lean logical axioms.')
