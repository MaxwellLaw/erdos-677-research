#!/usr/bin/env python3
"""Connect verified finite orbit/log data to the original 24 height intervals."""
from pathlib import Path
from fractions import Fraction as Q
import json,argparse
from export_log_certificates import bounds,rat
ROOT=Path(__file__).resolve().parents[1]

def log_bounds(N):
    e=N.bit_length()-1;shift=max(0,e-59);mant,rem=divmod(N,1<<shift);den=1<<(e-shift)
    slo,shi=Q(mant,den),Q(mant+(rem>0),den)
    _,l2,u2=bounds(Q(2));_,ll,_=bounds(slo);_,_,uu=bounds(shi)
    return Q(((e*l2+ll)*(1<<48)).__floor__(),1<<48),Q(((e*u2+uu)*(1<<48)).__ceil__(),1<<48)

def render():
    hs=json.loads((ROOT/'cas/height-bounds/height_intervals.json').read_text())['curves']
    cs=json.loads((ROOT/'cas/height-bounds/duplication_bounds.json').read_text())['curves']
    out='''/-
Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
-/
import LcmSix.HeightEnclosure
import LcmSix.HeightOrbits
import LcmSix.LogCertificates

/-!
# Actual canonical-height intervals for all 24 certificate points
Every orbit, primitivity, logarithm and finite rounding premise is discharged.
These are the original saved N=7 intervals, not assumed numerical hypotheses.
-/
namespace LcmSix.HeightIntervals
open EllipticDuplication HeightEnclosure
'''
    for h,c in zip(hs,cs,strict=True):
        branch='Branch'+'_'.join(map(str,c['pair']));model='PrimitiveDynamics.'+branch[0].lower()+branch[1:]
        C,D=c['upper_coefficient_C'],c['lower_coefficient_D'];_,uC=log_bounds(C);_,uD=log_bounds(D)
        assert 32*c['resultant_abs']<D
        for r in h['height_records']:
            label=r['label'].replace('P1+P2','S12').replace('P1+P3','S13').replace('P2+P3','S23');name=branch+'_'+label
            N=max(abs(int(r['iterate_x_numerator_hex'],16)),int(r['iterate_x_denominator_hex'],16))
            lB,uB=log_bounds(N);lo,hi=map(Q,r['canonical_H_interval'])
            assert lo<=(lB-uD/3)/16384 and (uB+uC/3)/16384<=hi
            out+=f'''\ntheorem {name}_height : ({rat(lo)}:ℝ)≤canonicalHeight {model} HeightPoints.{branch}.{label} ∧
    canonicalHeight {model} HeightPoints.{branch}.{label}≤({rat(hi)}:ℝ) := by
  apply from_seven_steps {model} HeightPoints.{branch}.{label}
    (HeightOrbits.{branch}.{label}.B:ℝ) {D} {rat(lB)} {rat(uB)} {rat(uC)} {rat(uD)} {rat(lo)} {rat(hi)}
  · exact HeightOrbits.{branch}.{label}.height7
  · norm_num [{model}]
  · simpa only [LogCertificates.{name}_size,HeightOrbits.{branch}.{label}.B,
      Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,Int.cast_ofNat] using LogCertificates.{name}_log
  · change Real.log ({C}:ℝ)≤({rat(uC)}:ℝ)
    simpa only [LogCertificates.{branch}_C_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.{branch}_C_log.2
  · simpa only [LogCertificates.{branch}_D_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.{branch}_D_log.2
  · norm_num
  · norm_num
'''
    return out+'\nend LcmSix.HeightIntervals\n'

def main():
    if not __debug__: raise RuntimeError('Verification requires assertions enabled')
    ap=argparse.ArgumentParser();ap.add_argument('--write',action='store_true');args=ap.parse_args();p=ROOT/'LcmSix/HeightIntervals.lean';s=render()
    if args.write:p.write_text(s)
    else: assert p.read_text()==s,'height interval source differs from original certificates'
    print('PASS: 24 original height intervals matched; generated Lean '+('written' if args.write else 'checked'))
if __name__=='__main__':main()
