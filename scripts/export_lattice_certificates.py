#!/usr/bin/env python3
"""Export integral dual witnesses for Lean; default mode checks saved artifacts.

Witness discovery is untrusted. Lean proves every generated integer obligation
and the resulting universal squared-distance bound. No inverse-matrix or LLL
assertion is used as a Lean assumption. This does not formalize the real logs.
"""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import hashlib
import json
import math
import sys

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'cas' / 'global-bound'
sys.path.insert(0, str(BASE))
from verify_lattice_certificate import matrix, transpose, inverse

HEADER = '/-\nCopyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.\n-/\n'
FIELDS = 'a1 a2 a3 a0 target w1 w2 w3 w4 denominator q1 q2 q3 q4 qt remainder delta threshold'.split()

def artifacts():
    raw = (BASE / 'lattice_reduction.json').read_bytes()
    data = json.loads(raw)
    certs = []
    out = ['import LcmSix.LatticeDistance\n\nnamespace LcmSix.LatticeDistance\n']
    assert [c['pair'] for c in data['curves']] == [[1,2],[1,5],[1,10],[2,5]]
    for curve in data['curves']:
        for j, step in enumerate(curve['steps']):
            name = 'step_' + '_'.join(map(str, curve['pair'])) + '_' + str(j)
            row = inverse(transpose(matrix(step['reduced_row_basis'])))[int(step['selected_inverse_row'])]
            d = math.lcm(*(x.denominator for x in row))
            w = [int(x*d) for x in row]
            a = list(map(int, step['rounded_basis_logs']))
            a0, target = int(step['rounded_real_period']), int(step['rounded_target'])
            quotients = []
            for numerator in [w[i]+w[3]*a[i] for i in range(3)] + [w[3]*a0]:
                q, r = divmod(numerator, d)
                assert r == 0
                quotients.append(q)
            qt, r = divmod(w[3]*target, d)
            delta = min(r, d-r)
            bound = int(step['input_coefficient_bound'])
            cutoff = 3*bound+1+10**int(step['positive_scaled_log_lower_power10'])
            threshold = 3*bound**2+cutoff**2
            norm = sum(x*x for x in w)
            assert d > 0 and delta >= 0 and norm > 0
            assert Q(delta**2, norm) == Q(step['distance_squared_lower'])
            assert norm*threshold < delta**2
            c = dict(zip(FIELDS, a+[a0,target]+w+[d]+quotients+[qt,r,delta,threshold], strict=True))
            certs.append({'name': name, 'pair': curve['pair'], 'step': j,
                'input_bound': str(bound), 'last_coordinate_cutoff': str(cutoff),
                'certificate': {k:str(v) for k,v in c.items()}})
            out.append(f'def {name} : Certificate := {{\n' +
                '\n'.join('  '+k+' := '+str(v) for k,v in c.items()) + '\n}\n')
            out.append(f'theorem {name}_valid : {name}.Valid := by\n  norm_num [Certificate.Valid, {name}]\n')
            out.append(f'theorem {name}_distance (m1 m2 m3 m0 : ℤ) :\n'
                f'    {threshold} < m1^2+m2^2+m3^2+\n'
                f'      (({a[0]})*m1+({a[1]})*m2+({a[2]})*m3+({a0})*m0-({target}))^2 :=\n'
                f'  {name}.excludes_ball {name}_valid m1 m2 m3 m0\n')
    assert len(certs) == 25
    out.append('end LcmSix.LatticeDistance\n')
    record = {'source_sha256': hashlib.sha256(raw).hexdigest(),
              'scope': 'integer lattice squared-distance certificates only', 'certificates': certs}
    return {ROOT/'LcmSix'/'LatticeCertificates.lean': HEADER+'\n'.join(out),
            BASE/'dual_certificates.json': json.dumps(record, indent=2)+'\n'}

def main():
    if not __debug__:
        raise SystemExit('Do not disable certificate assertions with Python optimization')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='regenerate artifacts instead of comparing')
    args = parser.parse_args()
    for path, content in artifacts().items():
        if args.write:
            path.write_text(content)
        else:
            assert path.read_text() == content, f'generated artifact mismatch: {path}'
    print('PASS: all 25 integral dual certificates and Lean statements match the original lattice data.')

if __name__ == '__main__':
    main()
