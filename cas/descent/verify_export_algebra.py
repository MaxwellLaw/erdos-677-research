#!/usr/bin/env python3
"""Exact stdlib sanity certificates for exported cubic-field data, not 2-descent."""
import ast
from certificate_io import finish
from fractions import Fraction as Q
import hashlib
import itertools
import json
from math import isqrt
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
COEFFS = [(-1,-65,261),(-1,-408,6912),(1,-1633,97763),(1,-1633,32963)]
EXPECTED_DISC = [-11948,-67175,-3340300,-1590700]
BASIS_POINTS = [[(5,6),(13,38),(-7,18)],[(12,-60),(-4,92),(78,-666)],[(Q(221,4),Q(3387,8)),(14,279),(43,330)],[(23,-90),(17,-102),(-1,186)]]

def determinant(a):
    n=len(a)
    if n==1:return a[0][0]
    return sum((-1)**j*a[0][j]*determinant([row[:j]+row[j+1:] for row in a[1:]]) for j in range(n))

def add(a,b):return tuple(x+y for x,y in zip(a,b))
def scale(a,s):return tuple(x*s for x in a)
def mul(a,b,abc):
    out=[Q(0)]*5
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    a2,a4,a6=abc
    for j in (4,3):
        out[j-1]-=a2*out[j];out[j-2]-=a4*out[j];out[j-3]-=a6*out[j]
    return tuple(out[:3])
def matrix(a,abc):
    cols=[mul(a,tuple(Q(i==j) for i in range(3)),abc) for j in range(3)]
    return [[cols[j][i] for j in range(3)] for i in range(3)]
def norm(a,abc):return determinant(matrix(a,abc))
def trace(a,abc):
    m=matrix(a,abc);return sum(m[i][i] for i in range(3))
def expression(s,abc):
    def ev(n):
        if isinstance(n,ast.Constant) and type(n.value) is int:return (Q(n.value),Q(0),Q(0))
        if isinstance(n,ast.Name) and n.id=='theta':return (Q(0),Q(1),Q(0))
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return scale(ev(n.operand),-1)
        if isinstance(n,ast.BinOp):
            a,b=ev(n.left),ev(n.right)
            if isinstance(n.op,ast.Add):return add(a,b)
            if isinstance(n.op,ast.Sub):return add(a,scale(b,-1))
            if isinstance(n.op,ast.Mult):return mul(a,b,abc)
            if isinstance(n.op,ast.Div):
                assert b[1:]==(0,0) and b[0];return scale(a,1/b[0])
            if isinstance(n.op,ast.Pow):
                assert b[1:]==(0,0) and b[0] in (0,1,2)
                v=(Q(1),Q(0),Q(0))
                for _ in range(int(b[0])):v=mul(v,a,abc)
                return v
        raise ValueError(ast.dump(n))
    return ev(ast.parse(s.replace('^','**'),mode='eval').body)

def array(block,label):
    s=re.search(re.escape(label)+r' \[\n(.*?)\n\]',block,re.S).group(1)
    return [tuple(Q(x.strip()) for x in row.split(',')) for row in re.findall(r'\[([^\]]+)\]',s)]
def coordinates(v,basis):
    # The four exported bases have the triangular shape 1, theta, b.
    assert basis[:2]==[(1,0,0),(0,1,0)]
    t=v[2]/basis[2][2]
    return (v[0]-t*basis[2][0],v[1]-t*basis[2][1],t)
def prime(p):return p>=2 and all(p%d for d in range(2,isqrt(p)+1))

def main():
    if not __debug__:raise RuntimeError('Run without Python optimization: assertions are part of this checker.')
    src=ROOT/'raw_descent_fields.result.json';data=json.loads(src.read_text())
    assert data['success'] and not data['truncated'] and data['exit_code']==0
    s=data['stdout'];rows=[]
    for j,(abc,disc,pts) in enumerate(zip(COEFFS,EXPECTED_DISC,BASIS_POINTS),1):
        block=re.search(rf'BEGIN_CASE {j}\n(.*?)END_CASE {j}',s,re.S).group(1)
        basis=array(block,'MAXIMAL_ORDER_BASIS');units=array(block,'UNIT_GENERATORS')
        assert len(basis)==3 and len(units)==2
        table=[[coordinates(mul(a,b,abc),basis) for b in basis] for a in basis]
        assert all(q.denominator==1 for row in table for v in row for q in v)
        tr=[[trace(mul(a,b,abc),abc) for b in basis] for a in basis]
        computed_disc=determinant(tr);assert computed_disc==disc
        polynomial_disc=determinant([[trace(mul(a,b,abc),abc) for b in [(1,0,0),(0,1,0),(0,0,1)]] for a in [(1,0,0),(0,1,0),(0,0,1)]])
        idx=1/abs(determinant([list(v) for v in basis]));assert idx.denominator==1 and polynomial_disc==idx**2*disc
        # If the order were not maximal, some prime p with p^2 | disc
        # would admit an integral element in (1/p)O outside O.
        square_primes=[p for p in range(2,isqrt(abs(disc))+1) if prime(p) and disc%(p*p)==0]
        maximality=[]
        for p in square_primes:
            tested=0
            for coeff in itertools.product(range(p),repeat=3):
                if coeff==(0,0,0):continue
                v=(Q(0),Q(0),Q(0))
                for c,b in zip(coeff,basis):v=add(v,scale(b,Q(c,p)))
                t=trace(v,abc);s2=(t*t-trace(mul(v,v,abc),abc))/2;n=norm(v,abc)
                assert any(z.denominator!=1 for z in (t,s2,n)), (j,p,coeff)
                tested+=1
            maximality.append({'prime':p,'nonzero_cosets_rejected':tested})
        unitnorms=[norm(u,abc) for u in units];assert all(n in (-1,1) for n in unitnorms)
        assert all(q.denominator==1 for u in units for q in coordinates(u,basis))
        reps=[expression(x,abc) for x in re.findall(r'SELMER_REPRESENTATIVE \d+ ([^\n]+)',block)]
        assert len(reps)==3
        repnorms=[norm(v,abc) for v in reps]
        def square(q):return q>=0 and isqrt(q.numerator)**2==q.numerator and isqrt(q.denominator)**2==q.denominator
        assert all(square(q) and q>0 for q in repnorms)
        pointnorms=[]
        for x,y in pts:
            n=norm((Q(x),Q(-1),Q(0)),abc);assert n==Q(y)**2;pointnorms.append(n)
        a2,a4,a6=abc
        irreducible_p=next(p for p in range(2,100) if prime(p) and all((x**3+a2*x*x+a4*x+a6)%p for x in range(p)))
        rows.append({'case':j,'a2_a4_a6':abc,'irreducible_mod_prime':irreducible_p,'order_basis':basis,'order_multiplication_table':table,'order_trace_gram':tr,'order_discriminant':computed_disc,'power_basis_discriminant':polynomial_disc,'power_order_index':idx,'exported_units':units,'unit_norms':unitnorms,'maximality_coset_checks':maximality,'selmer_representatives':reps,'selmer_representative_norms':repnorms,'supplied_point_norms':pointnorms})
    out={'status':'exact algebra checks only; not fundamental-unit generation, class-group completeness, Selmer completeness, or full Mordell-Weil generation','source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'curves':rows}
    dest=ROOT/'export_algebra_checks.json';digest=finish(dest,out)
    print('PASS: 4 maximal orders, trace discriminants, units, square norms and irreducibility witnesses')
    print('output_sha256',digest)
if __name__=='__main__':main()
