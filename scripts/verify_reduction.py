#!/usr/bin/env python3
"""Independent exact-arithmetic sanity checks, NOT a noncollision proof.

The universal reductions are proved in the accompanying mathematical audit and
Lean modules. All loops here have finite scope and no completeness claim.
"""
import json
import math
import platform
from collections import Counter


def product(n):
    return math.prod(n + i for i in range(1, 7))


def defect(n):
    return 12 * (2 if n % 4 >= 2 else 1) * (5 if n % 5 == 4 else 1)


def phi(t):
    return (t - 1) * (t - 9) * (t - 25)


def crt_fourth(q):
    odd_part = q
    two_part = 1
    while odd_part % 2 == 0:
        odd_part //= 2
        two_part *= 2
    A, B = 4 * two_part, 5 * odd_part
    assert math.gcd(A, B) == 1 and A * B == 20 * q
    c = (B - 1 + B * ((A - 3 - (B - 1)) * pow(B, -1, A) % A)) % (A * B)
    return 20 * q - 2, c + 40 * q


def carry(a, b, n, m):
    return a * defect(m) == b * defect(n)


def main():
    n_count = 10000
    for n in range(n_count):
        assert product(n) == defect(n) * math.lcm(*(n + i for i in range(1, 7)))
        assert phi((2 * n + 7) ** 2) == 64 * product(n)
    pairs = ((1, 2), (1, 5), (1, 10), (2, 5))
    counts = Counter()
    for n in range(20):
        for m in range(20):
            gn, gm = defect(n), defect(m)
            if gm > gn:
                h = math.gcd(gn, gm)
                ab = gn // h, gm // h
                assert ab in pairs
                counts[ab] += 1
    moduli = sorted(set(range(1, 201)) | {2**k for k in range(1, 40)} |
                    {5**k for k in range(1, 30)} | {30**k for k in range(1, 20)})
    for q in moduli:
        examples = ((1, 2, 20*q-3, 40*q-2),
                    (1, 5, 20*q-2, 40*q-1),
                    (1, 10, 20*q-3, 40*q-1),
                    (2, 5, *crt_fourth(q)))
        for a, b, n, m in examples:
            assert n >= 0 and m >= n + 6
            assert carry(a, b, n, m)
            assert (a*product(m)-b*product(n)) % q == 0
    # Exact arithmetic supporting opposite signs of the two critical values.
    assert 7168**2 * 7 > 10240**2
    # Exact square-divisor upper bounds for positive odd common centers.
    gcd_limits = []
    for a, b in pairs:
        C = 225 * (b - a)
        ds = [d for d in range(1, math.isqrt(C)+1, 2) if C % (d*d) == 0]
        largest = max(ds)
        assert all(largest % d == 0 for d in ds)
        gcd_limits.append({"pair": [a,b], "odd_d_must_divide": largest})
    print(json.dumps({
        "python": platform.python_version(),
        "scope": "Finite exact-arithmetic checks of reduction formulas; no noncollision claim",
        "product_lcm_identity_checked_n": [0, n_count-1],
        "coefficient_residue_class_counts": {str(k):v for k,v in counts.items()},
        "modular_construction_checked_moduli_count": len(moduli),
        "largest_modulus_checked": max(moduli),
        "gcd_limits": gcd_limits,
        "status": "all assertions passed",
    }, indent=2))


if __name__ == "__main__":
    main()
