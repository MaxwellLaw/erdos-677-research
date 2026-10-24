#!/usr/bin/env python3
"""Exact arithmetic for the documented David-bound proof. No floating point.
This does not prove David's theorem, period formulas, height theory or calculus.
"""
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import argparse, hashlib, json, sys


def main():
    if not __debug__:
        raise SystemExit('Assertions must remain enabled; do not run with -O.')
    ap=argparse.ArgumentParser()
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    base=Path(__file__).resolve().parent
    inputs={
        'height_parameters.json':base/'height_parameters.json',
        'period_parameters.json':base/'period_parameters.json',
    }
    # Source hashes identify the already inspected primary texts; this run does
    # not download or recheck the PDF files. See INITIAL_BOUND.md for retrieval.
    cited_sources={
        'David1995.pdf':'aefffcbf1d8475a4f17ce95a0de0240db687a9108d0ced5d8d972c844dc504ae',
        'Tzanakis1996.pdf':'00beb2e622143f0847590c85ca4adf07fecfb380468d68dc77e6f70ff7a203ff',
    }
    hashes={name:hashlib.sha256(path.read_bytes()).hexdigest() for name,path in inputs.items()}
    period=json.loads(inputs['period_parameters.json'].read_text())
    assert len(period['curves'])==4
    for row in period['curves']:
        lo,hi=map(Q,row['m'])
        assert row['cubic_discriminant']<0 and 0<lo<=hi<Q(999,1000)
        assert 4/(1-hi)<4000<64**2
    k,D,A=5,3,1000
    assert Q(29,10)*10**(6+6*k)==29*10**35
    assert 2*k*k+9*k+Q(123,10)==Q(1073,10)<108
    assert 2*k+2==12 and 2*k+1==11 and k+1==6
    # Round the only noninteger power 6^(1073/10) upward to 6^108.
    cupper=29*10**35*4**50*6**108*3**12*1000**5
    assert cupper<10**172
    e3lower=sum((Q(3**j,factorial(j)) for j in range(9)),Q(0))
    assert e3lower>20
    assert 20**3>1300
    assert 2000*34**6<10**13
    assert 4*64<1000 and 3*22==66
    # At t0=log(10^100)<300, F(t0)<2000*34^6<10^13.
    assert 1303<2000
    assert Q(1,1003)+Q(6,25000)<Q(7,1000)<1
    assert 26892<2**15
    m0=10**100
    assert Q(m0*m0,200)>10**197>10**185
    assert Q(m0*m0,200)>20
    out={
        'status':'Exact constants pass; mathematical theorem/period/height/calculus argument is in README.md, outside Lean',
        'python_version':sys.version,
        'cited_source_sha256':cited_sources,
        'input_sha256':hashes,
        'david_elliptic_factors':k,
        'nonperiod_logarithms':4,
        'field_degree':D,
        'common_logV':A,
        'auxiliary_E':'exp(1)',
        'logB':'max(log N, 1000/3, 66)',
        'N':'max(1,abs(m0),abs(m1),abs(m2),abs(m3)) <= 3 M + 1',
        'rounded_david_coefficient':str(cupper),
        'rounded_david_coefficient_strict_upper':'10^172',
        'e3_positive_series_lower':str(e3lower),
        'F_at_logM0_upper_integer':2000*34**6,
        'F_at_logM0_strict_upper':'10^13',
        'proposed_verified_initial_coefficient_cutoff':'M < 10^100',
        'scope':'Admissible points in the explicit rank-three subgroup; whole rational group additionally uses external Magma full-basis verification',
        'not_proved':['complete LLL reduction','complete residual point enumeration','k=6 noncollision','general Erdos677','Lean formalization of this analytic bound'],
    }
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print('PASS: exact David constants and scalar cutoff comparisons; read README.md for mathematical hypotheses.')

if __name__=='__main__':main()
