#!/usr/bin/env python3
# Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
"""Replay all independent arithmetic checks, without modifying the repository."""
from fractions import Fraction
from pathlib import Path
import hashlib,json,subprocess,sys

HERE=Path(__file__).resolve().parent

def run(script,*arguments):
    completed=subprocess.run([sys.executable,str(HERE/script),*map(str,arguments)],
        check=True,capture_output=True,text=True)
    result=json.loads(completed.stdout)
    assert result.get('result',result.get('status'))=='PASS'
    return result

def main():
    if not __debug__:raise SystemExit('Keep assertions enabled; do not use python -O.')
    finite=json.loads((HERE/'finite_saturation.json').read_text())
    small=json.loads((HERE/'small_height_certificate.json').read_text())
    heights_path=HERE.parent/'height-bounds/height_intervals.json'
    heights_raw=heights_path.read_bytes();heights=json.loads(heights_raw)
    assert hashlib.sha256(heights_raw).hexdigest()==small['source_height_intervals_sha256']
    assert len(finite['curves'])==len(small['curves'])==len(heights['curves'])==4
    for f,s,h in zip(finite['curves'],small['curves'],heights['curves'],strict=True):
        assert f['pair']==s['pair']==h['pair']
        a,b,c=s['a2_a4_a6']
        assert f['a2_a4_a6']==[a,b,c] and h['a_invariants']==[0,a,0,b,c]
        assert [[Fraction(z) for z in P] for P in f['basis']]==[[Fraction(z) for z in P] for P in h['basis']]
    a=run('verify_finite_saturation.py',HERE/'finite_saturation.json')
    b=run('verify_small_height.py')
    assert a['certificate_sha256']==hashlib.sha256((HERE/'finite_saturation.json').read_bytes()).hexdigest()
    assert b['certificate_sha256']==hashlib.sha256((HERE/'small_height_certificate.json').read_bytes()).hexdigest()
    print('PASS: exact torsion and 104 prime-saturation matrices; 294 complete finite-group cycles.')
    print('PASS: stronger global height bounds, all 51 small-height-box points, and regulator upper bounds.')
    print('PASS: curve/basis/input hashes agree with the existing height certificates.')
    print('Scope: arithmetic certificates with a documented human proof of complete saturation; rank upper bounds are certified separately in cas/descent; a complete Lean k=6 endpoint remains unfinished.')

if __name__=='__main__':main()
