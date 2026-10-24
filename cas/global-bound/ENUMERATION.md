# Complete residual box enumeration

2026-10-24, Asia/Shanghai. This is an exact Python computation with a human
mathematical completeness argument. It is not Lean-kernel verification. It
covers precisely the coefficient boxes supplied by the preceding lattice
certificate. Coverage of all rational points additionally depends on the
recorded Magma full-group basis certification; coverage of all original
length-six collisions additionally uses the elementary four-curve reduction.
Together with the proved initial bound and lattice reduction, this excludes
all original target pairs whose forward images lie in the explicit rank-three
subgroups. Invoking the external Magma full-basis flags yields the corresponding
computational k=6 corollary. There is no Lean k=6 endpoint here. It does not
address arbitrary k.

## Inputs, executed command, and result

The models and basis points are the same ordered triples as in
`../CAS.md`. The inverse maps are checked structurally
against `../verify_k6_maps.output.json` at startup. The
verifier parses only polynomial arithmetic from the JSON; it does not execute
source strings. All inverse polynomials are multiplied by four to have
integer coefficients without changing their ratios.

The bound source is `lattice_reduction.json`, whose
four `final_closed_coefficient_bound` fields give `[60,60,62,64]`. The exact
byte hash of that source is recorded in the output. No manual production bound
is accepted. The separate exact lattice verifier and its scope are described in
[LATTICE.md](LATTICE.md).

Executed from this directory:

```
python3 enumerate_residual.py \
  --bound-json lattice_reduction.json --prime-count 30 \
  --output reproduced-residual.json
```

| (a,b) | closed bound | triples tested | survivors after 30 primes |
|---|---:|---:|---:|
| (1,2) | 60 | 1771561 | 12 |
| (1,5) | 60 | 1771561 | 11 |
| (1,10) | 62 | 1953125 | 12 |
| (2,5) | 64 | 2146689 | 11 |

The last exact rational checks leave **no admissible disjoint interval pair**
in any of these boxes. The only surviving integer-square pairs with both
coordinates at least 49 are:

| (a,b) | U,V | outcome |
|---|---|---|
| (1,2) | 1089,1369 | n=13,m=15; gap 2 |
| (1,2) | 289,361 | n=5,m=6; gap 1 |
| (1,5) | 64,100 | even square roots, incompatible with 2n+7 and 2m+7 |
| (2,5) | 169,225 | n=3,m=4; gap 1 |

In (1,10), the additional nonexceptional survivors beyond the small boundary
points have noninteger inverse coordinates. Every branch also retains the
elliptic identity and one rational zero of the inverse denominator until the
exact phase; these are excluded by the established target-chart argument.
Eight further survivors per branch have U<49 or V<49.

The artifact and replay records are maintained in
[VERIFICATION.md](../../docs/VERIFICATION.md).
The output records each sieve's exact prime, group order, generator, basis
indices, allowed indices, tested/rejected/retained counts, and hashes of the
full group table and retained packed coefficient indices. Each final survivor
has its triple, full exact rational point and inverse coordinates (where the
inverse is defined), their hashes, and classification. The largest coordinate
uses only 20 bits; no large value is withheld behind a hash.

## Why the modular sieve cannot remove a target

Only primes p>5 not dividing the cubic discriminant are used. For these primes
the integral equation is a smooth elliptic curve over Z_p. Its projective
reduction map is a group homomorphism. See Milne, *Elliptic Curves*, second
edition, Chapter II §4, printed pp. 62–63, especially the homomorphism preceding
Theorem 4.1 and part (b):
[official text](https://www.jmilne.org/math/Books/EC2.pdf).
The source was read on 2026-10-24. Milne writes a short Weierstrass equation;
the shift x -> x+a2/3 is an invertible integral change at our p>5, so the same
statement applies to the displayed models. At good reduction all points are
in E0(Q_p), and hence all rational points admit this group-compatible reduction.

At a fixed prime the script enumerates every affine point by evaluating the
cubic for all x in F_p and using the exact table of square roots, and adds O.
For a chosen cyclic prime it constructs a generator G and all multiples
0,G,...,(N-1)G, verifying both NG=O and equality of this list as a set with the
entire previously enumerated curve. Thus the list has no missing or duplicated
point. Primes with no full-order generator are simply not used. The three
basis points are reduced and located in this table, yielding exact indices
d1,d2,d3. Reduction of a coefficient triple consequently has table index
`m1*d1+m2*d2+m3*d3 mod N`.

If the reduced point is O, it is **retained**. If it is affine but its
integer-cleared inverse denominator D is zero modulo p, it is also **retained**.
Otherwise its rational affine coordinates are p-integral: primitive
projective coordinates with nonzero last coordinate reduce to the affine
chart. The three integer inverse polynomials can therefore be evaluated
modulo p, and the denominator is a unit. Evaluation commutes with reduction,
so the computed residues of Nu/D and Nv/D are the residues of the original
U and V. If U and V are integer squares, both residues must be squares in F_p,
including zero. Therefore rejecting a nonsquare residue is sound.

This argument deliberately makes no inference from an undefined inverse
modulo p. Even if the rational point's coordinate denominators are divisible
by p, it reduces to O and is retained. Exceptional reductions can only enlarge
the candidate set; they cannot cause a missing solution. The sieve does not
assume that birational maps preserve integrality.

## Exhaustion and the exact final tests

For each B the nested loops explicitly enumerate all `(2B+1)^3` triples with
`-B<=mi<=B`, including zero, all signs, and the endpoints. Their packing as
base-(2B+1) indices is bijective. Later sieves only filter these stored indices;
they never replace the coefficient range with a guessed smaller one.

Each survivor is reconstructed from the original rational basis with exact
Fractions and the tangent/chord group law. The script checks membership in
the elliptic curve and, when D!=0, verifies the original cubic equation after
applying the inverse. It then checks, in order:

1. U,V are integers and at least 49.
2. Their nonnegative integer square roots X,Y square back exactly.
3. X,Y are odd, so n=(X-7)/2 and m=(Y-7)/2 are nonnegative integers.
4. Y-X>=12, exactly the original disjointness condition m>=n+6.
5. If all prior tests pass, compare the two original exact six-term LCMs.

No disjoint candidate reaches test 5 in this computation. For review, the
script additionally evaluates the three overlapping odd-square candidates
exactly: their equal LCMs are 1627920 for (13,15), 27720 for (5,6), and 2520
for (3,4). These are not counterexamples to the original problem. The exclusions are therefore
already forced by necessary conditions; no carry condition is assumed
sufficient. The known proof that target points have finite forward image and
D<0 excludes the rational identity and D=0 points. That chart proof is in the
previous exact map verification; it is not inferred from this finite search.

## Second implementation

[verify_residual_independent.py](verify_residual_independent.py) exhausts the
same four boxes using 30 good primes greater than 257, disjoint from all
primes in the primary computation. It enumerates the complete finite curve
and constructs translation permutations for the basis points; it does not
choose a cyclic generator or compute discrete logarithms, and it also uses
noncyclic groups. Its coefficient packing and iteration order differ from the
primary sieve. A separate rational group-law implementation reconstructs the
survivors, and its own restricted parser reads the inverse expressions.

The second implementation finds the same 46 coefficient triples and exact
rational point and inverse coordinates, with the same exclusions. The record
is [residual_independent.json](residual_independent.json). This is a second
implementation and prime set, distinct from merely rerunning the primary
script. Both computations retain the same external analytic and full-group
obligations described above.

Reproduce from this directory:

```sh
python3 verify_residual_independent.py \
  --bounds lattice_reduction.json --maps ../verify_k6_maps.output.json \
  --basis-input real_logs.json --output reproduced-independent.json
```

## Algorithm tests and trust boundary

The `--self-test` mode checked all 125 triples in the B=2 box for
each curve against direct rational reconstruction and reduction at three
primes. It also checked that the two previously documented overlapping
integer-square examples survive all 30 selected modular conditions. These
are regression checks of the algorithm, not substitutes for the preceding
mathematical sieve proof. An initial 20-prime version ran before production;
the subsequent replay with the same 30-prime tables used in production also
passed. Reproduce it from this directory with:

```sh
python3 enumerate_residual.py --self-test --prime-count 30 \
  --output reproduced-self-test.json
```

The production implementation uses only Python standard-library integer and
Fraction arithmetic. Assertions must remain enabled. None of the reduction
homomorphism, elliptic group law, analytic coefficient bound, or this Python
enumeration is silently added as a Lean axiom. A final Lean endpoint requires
its own corresponding proofs or kernel-checked certificates. The absence of
survivors in a box chosen without a proved bound would not solve k=6; here the
bound is a separate explicit input whose validity must be reviewed together
with this computation.
