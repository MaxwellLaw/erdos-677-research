#!/usr/bin/env python3
"""Export/check exact Lean Gram interval and LDL certificates.

The exporter is untrusted: Lean checks all numerical obligations. The generated
height-to-quadratic-form endpoints retain six explicit height interval premises
per curve; this script does not prove those height intervals or actual orbits.
Author: MaxwellLaw.
"""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT/'cas'/'height-bounds'/'height_intervals.json'
EXPECTED_SHA = '2a988af3758fc58d84e7220160fc608e73194f703033099c96a97b580595f450'
TARGET = ROOT/'LcmSix'/'GramCertificates.lean'
HEADER = '''/-
Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
-/
import LcmSix.GramBounds

/-!
# Four exact rational Gram lower-bound certificates

Generated from height_intervals.json by scripts/export_gram_certificates.py.
All entries, radii, LDL identities and positivity are kernel checked. Each
height conclusion explicitly assumes six closed height intervals. No actual
elliptic point or orbit-height interval is asserted by these conditional
bridges; the separate actual-point development must discharge those premises.
-/

namespace LcmSix.GramBounds
'''


def leanq(x):
    x=Q(x)
    if x.denominator == 1:
        return f'({x.numerator} : ℝ)'
    return f'({x.numerator}/{x.denominator} : ℝ)'


def symdef(name,m):
    pairs=[('d1',0,0),('d2',1,1),('d3',2,2),('e12',0,1),('e13',0,2),('e23',1,2)]
    return f'noncomputable def {name} : Sym3 where\n'+''.join(
        f'  {key} := {leanq(m[i][j])}\n' for key,i,j in pairs)


def artifacts():
    raw=SOURCE.read_bytes()
    assert hashlib.sha256(raw).hexdigest()==EXPECTED_SHA
    data=json.loads(raw)
    assert [c['pair'] for c in data['curves']]==[[1,2],[1,5],[1,10],[2,5]]
    out=[HEADER]
    labels=['h1','h2','h3','h12','h13','h23']
    for c in data['curves']:
        name='branch'+'_'.join(map(str,c['pair']))
        iv=[[tuple(map(Q,e)) for e in row] for row in c['pairing_intervals']]
        assert all(iv[i][j]==iv[j][i] for i in range(3) for j in range(3))
        mid=[[(l+u)/2 for l,u in row] for row in iv]
        rad=[[(u-l)/2 for l,u in row] for row in iv]
        rho=Q(c['max_radius_row_sum'])
        assert rho==max(map(sum,rad))
        shift=Q(1,100)+rho
        mat=[[mid[i][j]-(shift if i==j else 0) for j in range(3)] for i in range(3)]
        assert mat==[list(map(Q,row)) for row in c['midpoint_minus_lambda_plus_radius_identity']]
        d1=mat[0][0]
        l21=mat[0][1]/d1
        l31=mat[0][2]/d1
        d2=mat[1][1]-d1*l21*l21
        l32=(mat[1][2]-d1*l21*l31)/d2
        d3=mat[2][2]-d1*l31*l31-d2*l32*l32
        assert min(d1,d2,d3)>0
        assert [d1,d1*d2,d1*d2*d3]==list(map(Q,c['leading_principal_minors']))
        out.append(symdef(name+'_midpoint',mid))
        out.append(symdef(name+'_radius',rad))
        out.append(f'noncomputable def {name}_rho : ℝ := {leanq(rho)}\n')
        out.append(f'noncomputable def {name}_squares : SquareCertificate where\n'+''.join(
            f'  {key} := {leanq(v)}\n' for key,v in
            [('d1',d1),('d2',d2),('d3',d3),('l21',l21),('l31',l31),('l32',l32)]))
        out.append(f'''theorem {name}_squares_valid :
    {name}_squares.Valid {name}_midpoint ((1/100 : ℝ)+{name}_rho) := by
  norm_num [SquareCertificate.Valid,{name}_squares,{name}_midpoint,{name}_rho]
''')
        out.append(f'''theorem {name}_row_radii :
    {name}_radius.d1+{name}_radius.e12+{name}_radius.e13 ≤ {name}_rho ∧
    {name}_radius.d2+{name}_radius.e12+{name}_radius.e23 ≤ {name}_rho ∧
    {name}_radius.d3+{name}_radius.e13+{name}_radius.e23 ≤ {name}_rho := by
  norm_num [{name}_radius,{name}_rho]
''')
        hvalues=[tuple(map(Q,r['canonical_H_interval'])) for r in c['height_records']]
        assert [r['label'] for r in c['height_records']]==['P1','P2','P3','P1+P2','P1+P3','P2+P3']
        args='    (h1 h2 h3 h12 h13 h23 : ℝ)\n'+''.join(
            f'    (h_{label} : {leanq(lo)} ≤ {label} ∧ {label} ≤ {leanq(hi)})\n'
            for label,(lo,hi) in zip(labels,hvalues))
        used=', '.join(f'h_{h}.{i}' for h in labels for i in [1,2])
        out.append(f'''/-- Convert six explicit height intervals into the symmetric pairing intervals. -/
theorem {name}_height_entries
{args}    : EntryBounds (fromHeights h1 h2 h3 h12 h13 h23) {name}_midpoint {name}_radius := by
  simp only [EntryBounds,fromHeights,{name}_midpoint,{name}_radius,abs_le]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    linarith only [{used}]
''')
        hypotheses=' '.join('h_'+s for s in labels)
        out.append(f'''/-- A conditional lower bound for all real coefficient triples. -/
theorem {name}_height_lower
{args}    (x y z : ℝ) :
    (x^2+y^2+z^2)/100 ≤
      h1*x^2+h2*y^2+h3*z^2+(h12-h1-h2)*x*y+
        (h13-h1-h3)*x*z+(h23-h2-h3)*y*z := by
  obtain ⟨hr1,hr2,hr3⟩ := {name}_row_radii
  have h := certified_lower (fromHeights h1 h2 h3 h12 h13 h23)
    {name}_midpoint {name}_radius {name}_rho (1/100) {name}_squares
    {name}_squares_valid
    ({name}_height_entries h1 h2 h3 h12 h13 h23 {hypotheses})
    hr1 hr2 hr3 x y z
  rw [quad_fromHeights] at h
  have he : (1/100 : ℝ)*(x^2+y^2+z^2)=(x^2+y^2+z^2)/100 := by ring
  rw [he] at h
  exact h
''')
        out.append(f'''/-- The same conditional bound for arbitrary integer coefficient triples. -/
theorem {name}_integer_lower
{args}    (m : Fin 3 → ℤ) :
    ((m 0 : ℝ)^2+(m 1 : ℝ)^2+(m 2 : ℝ)^2)/100 ≤
      h1*(m 0 : ℝ)^2+h2*(m 1 : ℝ)^2+h3*(m 2 : ℝ)^2+
        (h12-h1-h2)*(m 0 : ℝ)*(m 1 : ℝ)+
        (h13-h1-h3)*(m 0 : ℝ)*(m 2 : ℝ)+
        (h23-h2-h3)*(m 1 : ℝ)*(m 2 : ℝ) :=
  {name}_height_lower h1 h2 h3 h12 h13 h23 {hypotheses} (m 0) (m 1) (m 2)
''')
    out.append('end LcmSix.GramBounds\n')
    return '\n'.join(out)


def main():
    if not __debug__:
        raise SystemExit('Assertions must remain enabled')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write',action='store_true')
    args=ap.parse_args()
    result=artifacts()
    if args.write:
        TARGET.write_text(result)
    else:
        assert TARGET.read_text()==result, 'Lean Gram certificate export mismatch'
    print('PASS: four exact Gram/LDL certificates and 24 explicit height premises match pinned data.')

if __name__=='__main__':
    main()
