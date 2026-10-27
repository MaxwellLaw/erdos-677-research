#!/usr/bin/env python3
"""Export untrusted finite arithmetic witnesses consumed by Lean's kernel.

Only the 24 fixed point records and their seven duplications are replayed.
No bounded search, CAS assertion, native_decide, or mathematical axiom is used.
The generated source proves the arithmetic; this exporter is not trusted.
"""
from fractions import Fraction
from math import gcd
from pathlib import Path
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'cas/height-bounds/height_intervals.json'
SOURCE_SHA = '2a988af3758fc58d84e7220160fc608e73194f703033099c96a97b580595f450'
TARGET = ROOT / 'LcmSix/HeightOrbits.lean'
MARKER = '-- BEGIN GENERATED FINITE ORBIT CERTIFICATES\n'
CLOSE = 'end LcmSix.HeightOrbits\n'


def bezout(p, q):
    r, s, t, rr, ss, tt = p, 1, 0, q, 0, 1
    while rr:
        k = r // rr
        r, rr = rr, r-k*rr
        s, ss = ss, s-k*ss
        t, tt = tt, t-k*tt
    assert r == 1 and s*p+t*q == 1
    return s, t


def generate():
    raw = SOURCE.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == SOURCE_SHA
    data = json.loads(raw)
    assert data['iterations'] == 7 and len(data['curves']) == 4
    lines = [MARKER.rstrip(), '-- Source height_intervals.json SHA256: '+SOURCE_SHA,
             '-- Regenerate: python3 scripts/export_height_orbits.py',
             'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '']
    for row in data['curves']:
        branch = 'Branch'+'_'.join(map(str, row['pair']))
        a, b, c = (row['a_invariants'][i] for i in (1, 3, 4))
        curve = f'(curve ({a}) ({b}) ({c})).Point'
        for record in row['height_records']:
            label = record['label'].replace('P1+P2','S12').replace('P1+P3','S13').replace('P2+P3','S23')
            point = f'HeightPoints.{branch}.{label}'
            x = Fraction(record['initial_point'][0])
            pairs, divisors = [(x.numerator, x.denominator)], []
            for _ in range(7):
                p, q = pairs[-1]
                f = p**4-2*b*p*p*q*q-8*c*p*q**3+(b*b-4*a*c)*q**4
                g = 4*(p**3*q+a*p*p*q*q+b*p*q**3+c*q**4)
                d = gcd(f,g)
                assert d > 0 and g != 0
                if g < 0:
                    d = -d
                pairs.append((f//d, g//d))
                divisors.append(d)
            p, q = pairs[-1]
            assert p == int(record['iterate_x_numerator_hex'],16)
            assert q == int(record['iterate_x_denominator_hex'],16)
            u, v = bezout(p,q)
            B = max(abs(p),q)
            ns = branch+'.'+label
            lines += ['namespace '+ns, '']
            for i,(p_i,q_i) in enumerate(pairs):
                lines += [f'def p{i} : ℤ := {hex(p_i)}', f'def q{i} : ℤ := {hex(q_i)}']
            lines += [f'def B : ℤ := {hex(B)}', '',
                      '/-- The final integer coordinates are primitive, by a checked Bezout witness. -/',
                      'theorem final_coprime : IsCoprime p7 q7 := by',
                      f'  exact ⟨({hex(u)}),({hex(v)}),by decide⟩', '',
                      'theorem B_pos : (0 : ℤ)<B := by decide', '',
                      'private theorem final_size : max |p7| |q7|=B := by decide', '']
            for i,d in enumerate(divisors):
                lines += [f'private theorem step{i} : ({d} : ℤ)≠0 ∧',
                          f'    HeightCertificates.F ({a}) ({b}) ({c}) p{i} q{i}=({d})*p{i+1} ∧',
                          f'    HeightCertificates.G ({a}) ({b}) ({c}) p{i} q{i}=({d})*q{i+1} := by decide', '']
            orbit = lambda n: f'((fun P : {curve} => P+P)^[{n}] {point})'
            lines += [f'private theorem rep0 : RawRepresents {orbit(0)} p0 q0 := by',
                      f'  change RawRepresents {point} p0 q0',
                      f'  refine ⟨(q0 : ℚ),by norm_num [q0],?_,?_⟩ <;>',
                      f'    rw [{point}_xRep] <;> norm_num [p0,q0]', '']
            for i in range(7):
                privacy = 'private ' if i < 6 else ''
                name = f'rep{i+1}' if i < 6 else 'final_represents'
                lines += [f'{privacy}theorem {name} : RawRepresents {orbit(i+1)} p{i+1} q{i+1} := by',
                          "  rw [Function.iterate_succ_apply']",
                          f'  have h := (raw_step (a:=({a})) (b:=({b})) (c:=({c})) rep{i}',
                          f'    step{i}.1 step{i}.2.1 step{i}.2.2)',
                          f'  change RawRepresents ({orbit(i)}+{orbit(i)}) p{i+1} q{i+1} at h',
                          '  exact h', '']
            lines += ['/-- Exact naive height of the actual seventh group-doubling iterate. -/',
                      f'theorem height7 : naiveHeight {orbit(7)}=Real.log (B : ℝ) :=',
                      '  naiveHeight_of_raw final_represents final_coprime final_size', '',
                      'end '+ns, '']
    return '\n'.join(lines)+'\n'+CLOSE


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--check', action='store_true', help='check generated bytes without writing')
    args = ap.parse_args()
    old = TARGET.read_text()
    if MARKER in old:
        prefix = old.split(MARKER)[0]
    else:
        assert old.endswith(CLOSE)
        prefix = old[:-len(CLOSE)]
    expected = prefix+generate()
    if args.check:
        assert expected == old, 'generated orbit source is out of date'
    else:
        TARGET.write_text(expected)
    print(('CHECKED' if args.check else 'EXPORTED')+' 24 fixed seven-step orbit certificates')
    print('SOURCE_SHA256', hashlib.sha256(expected.encode()).hexdigest())
    print('SOURCE_BYTES', len(expected.encode()))

if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('assertions must be enabled')
    main()
