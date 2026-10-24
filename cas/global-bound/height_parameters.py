#!/usr/bin/env python3
"""Exact arithmetic supporting explicit David-height parameter bounds.
The real-height implications are justified separately in README.md.
No period estimate, coefficient bound M0, or point completeness is asserted.
"""
from fractions import Fraction as Q
from math import factorial, gcd, lcm
from pathlib import Path
import hashlib
import json
import platform

HERE = Path(__file__).resolve().parent
if not __debug__: raise SystemExit("Assertions must remain enabled.")
HEIGHT_FILE = HERE.parent / "height-bounds/height_intervals.json"
DUP_FILE = HERE.parent / "height-bounds/duplication_bounds.json"
height_raw, dup_raw = HEIGHT_FILE.read_bytes(), DUP_FILE.read_bytes()
heights, dup = json.loads(height_raw), json.loads(dup_raw)
assert heights["constants_sha256"] == hashlib.sha256(dup_raw).hexdigest()
assert heights["uniform_height_error_certificate"]["S"] == 5

# pair, original model, x(Q0) numerator c+d*alpha, denominator b-a*alpha
DATA = [
    ((1,2), (-1,-65,261), (16,1)),
    ((1,5), (-1,-408,6912), (120,48)),
    ((1,10), (1,-1633,97763), (500,247)),
    ((2,5), (1,-1633,32963), (205,44)),
]

def exp_certificate(power, degree, lower):
    partial = sum((Q(power**j, factorial(j)) for j in range(degree+1)), Q(0))
    assert partial > lower
    return {"power": power, "degree": degree, "lower_target": lower,
            "positive_partial_sum": str(partial), "positive_gap": str(partial-lower)}

exp_certs = [exp_certificate(7,8,747), exp_certificate(3,3,10),
             exp_certificate(22,27,3011814400), exp_certificate(5,10,146)]
rows = []
for ((a,b),(a2,a4,a6),(c,d)), hr, dr in zip(DATA,heights["curves"],dup["curves"], strict=True):
    assert hr["pair"] == dr["pair"] == [a,b]
    assert hr["a_invariants"] == dr["a_invariants"] == [0,a2,0,a4,a6]
    assert gcd(a,b) == 1 and 1 < Q(b,a) <= 10
    # No b/a in this list is a rational cube, so alpha has degree exactly 3.
    assert (a,b) in [(1,2),(1,5),(1,10),(2,5)]
    A = Q(a4)-Q(a2*a2,3)
    B = Q(a6)-Q(a2*a4,3)+Q(2*a2**3,27)
    g2, g3 = -4*A, -4*B
    delta = g2**3 - 27*g3**2
    assert delta != 0
    j = 1728*g2**3/delta
    den = lcm(g2.denominator,g3.denominator)
    coords = [den,int(den*g2),int(den*g3)]
    assert gcd(*coords) == 1
    J = max(max(map(abs,coords)),abs(j.numerator),j.denominator)
    assert J <= 3011814400
    row_norm = max(abs(c)+abs(d),a+b)
    assert row_norm <= 747 and b <= 10
    assert a*c+b*d != 0
    assert dr["upper_coefficient_C"] < 146**3
    basis_upper = [Q(r["canonical_H_interval"][1]) for r in hr["height_records"][:3]]
    assert [r["label"] for r in hr["height_records"][:3]] == ["P1","P2","P3"]
    assert all(v < 5 for v in basis_upper)
    rows.append({"pair": [a,b], "original_a2_a4_a6": [a2,a4,a6],
                 "short_A_B": list(map(str,[A,B])), "David_g2_g3": list(map(str,[g2,g3])),
                 "David_discriminant": str(delta), "j": str(j),
                 "primitive_curve_height_coordinates": coords,
                 "curve_height_max_integer": J,
                 "x_Q0_linear_map_coefficient_abs_row_max": row_norm,
                 "x_Q0_linear_map_nonzero_determinant_abs": a*c+b*d,
                 "alpha_height": f"log({b})/3",
                 "h_x_Q0_upper": f"log({row_norm})+log({b})/3",
                 "h_x_Q0_strict_uniform_upper": 8,
                 "canonical_Hx_Q0_strict_uniform_upper": 13,
                 "David_canonical_Q0_strict_uniform_upper": "39/2",
                 "canonical_Hx_basis_certified_upper": list(map(str,basis_upper)),
                 "David_canonical_basis_strict_uniform_upper": "15/2",
                 "David_curve_h_strict_uniform_upper": 22})
print(json.dumps({"status": "exact arithmetic checks passed; height deductions are human proofs",
                  "python": platform.python_version(),
                  "height_input_sha256": hashlib.sha256(height_raw).hexdigest(),
                  "duplication_input_sha256": hashlib.sha256(dup_raw).hexdigest(),
                  "normalization": "David canonical plane height = (3/2) Hx",
                  "scope": "curve and point heights only; period terms and M0 not certified here",
                  "positive_exponential_partial_sums": exp_certs, "curves": rows}, indent=2))
