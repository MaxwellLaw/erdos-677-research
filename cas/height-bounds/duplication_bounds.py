"""Exact coefficient/Bezout certificates for the four duplication maps.
No complete integral-point claim. No floating point arithmetic.
"""
from pathlib import Path
import json
import sympy as s

rows=[]
models=[(-1,-65,261),(-1,-408,6912),(1,-1633,97763),(1,-1633,32963)]
pairs=[(1,2),(1,5),(1,10),(2,5)]
for ab,(a2,a4,a6) in zip(pairs,models):
    F=[1,0,-2*a4,-8*a6,a4*a4-4*a2*a6]
    G=[0,4,4*a2,4*a4,4*a6]
    M=s.zeros(8)
    for j in range(4):
        for i in range(5):
            M[i+j,j]=F[i]
            M[i+j,j+4]=G[i]
    det=int(M.det()); R=abs(det)
    assert R>0
    vectors=[]
    for k in [0,7]:
        v=M.inv()*s.eye(8)[:,k]*R
        assert all(x.q==1 for x in v)
        coeffs=[int(x) for x in v]
        target=[0]*8;target[k]=R
        assert list(M*s.Matrix(coeffs))==target
        vectors.append(coeffs)
    C=max(sum(abs(x) for x in F),sum(abs(x) for x in G))
    D=max(sum(abs(x) for x in v) for v in vectors)
    assert C>=1 and D>=1
    rows.append({'pair':ab,'a_invariants':[0,a2,0,a4,a6],
                 'F_coefficients_p_descending':F,'G_coefficients_p_descending':G,
                 'resultant_abs':R,'bezout_p7':vectors[0], 'bezout_q7':vectors[1],
                 'upper_coefficient_C':C,'lower_coefficient_D':D})
print(json.dumps({'status':'exact integer polynomial identities checked',
    'sympy':s.__version__,
    'meaning':'h(2P)-4h(P) lies between -log D and log C; canonical H-h between -log D/3 and log C/3',
    'curves':rows},indent=2))
