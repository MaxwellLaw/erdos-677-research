# Exact number-field inputs for 2-descent

These certificates independently verify maximal orders, unit squareclasses,
complete finite sets of ideal-class generators, and enough principal relations
to bound the four global norm-square spaces. They use standard algebraic
number theory and Python integer/rational arithmetic; they are not Lean proofs.
The elliptic-curve descent and local restriction are separate steps described
in [RANK_PROOF.md](RANK_PROOF.md).

The precise global conclusion here is

```
dim_F2 ker(Norm : K(S,2) -> Q*/Q*²) <= 3, 5, 3, 3
```

for the four cubic fields corresponding, in order, to ratios `(1,2)`, `(1,5)`,
`(1,10)`, `(2,5)`. Their definitions and the proof are in
[IDEAL_CERTIFICATES.md](IDEAL_CERTIFICATES.md). The second bound alone does not
prove rank at most three; it requires the separate local 3-adic restriction.

From the repository root, run the combined read-only check:

```sh
python3 cas/descent/verify_all.py
```

Its individual components are:

```sh
python3 cas/descent/verify_export_algebra.py
python3 cas/descent/verify_unit_squareclasses.py
python3 cas/descent/verify_class_relations.py
python3 cas/descent/verify_rank_support.py
python3 cas/descent/local3/verify_all.py
python3 cas/descent/audit_class_lattices.py
```

The local 3-adic component has its own [proof and verification description](local3/README.md).
The independent lattice audit checks each Hermite-normal-form result by Cramer
lattice membership and the gcd of all maximal minors, and checks quotient
characteristic polynomials using separate degree-at-most-three formulas.
Each command recomputes the exact certificate and compares every JSON field
with the stored output. The default does not overwrite certificates. Explicit
`--write` regenerates a file; Python optimization is rejected because assertions
are part of the checkers. These replays need only the Python standard library.

The original discovery scripts `raw_descent_fields.m` and
`class_s_relations_1.m` through `class_s_relations_4.m` were executed by the
official Magma calculator, version **2.30-1**, seed 550, on 25 October 2026
(Asia/Shanghai). A fresh external run, using a separate output path, is possible
with the existing runner, for example:

```sh
python3 cas/run_magma.py cas/descent/class_s_relations_1.m /tmp/class_s_relations_1.replay.json
```

The saved `.result.json` files are genuine successful transcripts. Intermediate
representatives and timings may vary between external runs. The certificate
checkers do not invoke Magma, trust its class-number flag, or use a claimed
Selmer dimension as a mathematical assumption. They check the exported concrete
algebraic witnesses. The raw Selmer/class/unit output remains available to
show how those witnesses were found. In particular, the recorded class-group
invariants `[2]`, `[27]`, `[3,6]`, `[6]` are not asserted as independently
certified exact class groups by these checkers; only the stated mod-2 upper
bounds are needed and proved.

| Certificate | SHA-256 |
|---|---|
| `export_algebra_checks.json` | `0b96e43c01b15e32908de5f4c9f40a6c9cb901145ebda9c7619f255387354a07` |
| `unit_squareclass_checks.json` | `dd8042fd81de19cb155b69e86e067dc3e897d440fd93fec54d2e4ec2886e3095` |
| `class_relation_checks.json` | `ef2b4252af44e510c4f5cce7db13f7befe382a15449772d7388332e70c51ce66` |

Each certificate also records hashes of its direct input artifacts. No external
paper PDF is redistributed in this directory. No claim about arbitrary interval
lengths, a Lean k=6 endpoint, or award eligibility follows from this directory
alone.

The author, MaxwellLaw, used AI as an assistive tool.
