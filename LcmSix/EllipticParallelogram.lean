/-
Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
-/
import LcmSix.EllipticAddSub
import LcmSix.CanonicalQuadratic
import Mathlib.NumberTheory.Height.EllipticCurve
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas

/-!
# The bounded naive parallelogram law and actual canonical pairing

The polynomial-map and symmetric-square height estimates and the addition-
subtraction polynomial certificates used here are due to Michael Stoll in
Mathlib. The projective height API also credits Ralf Stephan. The standard
canonical-height limiting and polarization argument is in CanonicalQuadratic.
-/

namespace LcmSix.EllipticParallelogram
open WeierstrassCurve Affine EllipticDuplication

/-- The symmetric-square height differs uniformly from the sum of x-heights.
Every point, including infinity, has a nonzero x-representative. -/
theorem sym2x_height_defect (W : WeierstrassCurve.Affine ℚ) :
    ∃ C : ℝ, ∀ P Q : W.Point,
      |Height.logHeight (P.sym2x Q) -
        (Height.logHeight P.xRep+Height.logHeight Q.xRep)| ≤ C := by
  obtain ⟨C,hC⟩ := Height.abs_logHeight_sym2_sub_le ℚ
  refine ⟨C,fun P Q => ?_⟩
  have hp : ![P.xRep 0,P.xRep 1]=P.xRep := by ext i; fin_cases i <;> rfl
  have hq : ![Q.xRep 0,Q.xRep 1]=Q.xRep := by ext i; fin_cases i <;> rfl
  have hpn : ![P.xRep 0,P.xRep 1]≠0 := by rw [hp]; exact P.xRep_ne_zero
  have hqn : ![Q.xRep 0,Q.xRep 1]≠0 := by rw [hq]; exact Q.xRep_ne_zero
  simpa only [hp,hq,Point.sym2x] using hC hpn hqn

/-- Every actual point pair satisfies the bounded naive parallelogram law.
The only curve hypothesis is nonsingularity of the model, discharged by the
four existing IsElliptic instances. -/
theorem naiveHeight_boundedDefect (a b c : ℚ) [(curve a b c).IsElliptic] :
    ∃ C : ℝ, CanonicalQuadratic.BoundedDefect (@naiveHeight a b c) C := by
  obtain ⟨D,hD⟩ := (curve a b c).abs_logHeight_addSubMap_sub_two_mul_logHeight_le
  obtain ⟨C,hC⟩ := sym2x_height_defect (curve a b c)
  refine ⟨D+3*C,fun P Q => ?_⟩
  obtain ⟨r,hr,he⟩ := EllipticAddSub.addSubMap_sym2x a b c P Q
  have hm := hD (P.sym2x Q)
  rw [he,Height.logHeight_smul_eq_logHeight _ hr] at hm
  obtain ⟨hml,hmu⟩ := abs_le.mp hm
  obtain ⟨hil,hiu⟩ := abs_le.mp (hC P Q)
  obtain ⟨hol,hou⟩ := abs_le.mp (hC (P+Q) (P-Q))
  dsimp only [naiveHeight]
  rw [abs_le]
  constructor <;> linarith

/-- Exact parallelogram law for the canonical height of the actual point group. -/
theorem canonical_parallelogram (M : PrimitiveDynamics.Model)
    [(curve M.a M.b M.c).IsElliptic] (P Q : (curve M.a M.b M.c).Point) :
    canonicalHeight M (P+Q)+canonicalHeight M (P-Q)=
      2*canonicalHeight M P+2*canonicalHeight M Q := by
  obtain ⟨C,hC⟩ := naiveHeight_boundedDefect M.a M.b M.c
  exact CanonicalQuadratic.parallelogram hC P Q

/-- The symmetric biadditive canonical pairing on the actual rational group. -/
noncomputable def canonicalPairing (M : PrimitiveDynamics.Model)
    [(curve M.a M.b M.c).IsElliptic] :
    (curve M.a M.b M.c).Point →+ (curve M.a M.b M.c).Point →+ ℝ :=
  CanonicalQuadratic.bilinear (canonical_parallelogram M)

theorem canonicalPairing_apply (M : PrimitiveDynamics.Model)
    [(curve M.a M.b M.c).IsElliptic] (P Q : (curve M.a M.b M.c).Point) :
    canonicalPairing M P Q=(canonicalHeight M (P+Q)-canonicalHeight M (P-Q))/4 := rfl

theorem canonicalPairing_symm (M : PrimitiveDynamics.Model)
    [(curve M.a M.b M.c).IsElliptic] (P Q : (curve M.a M.b M.c).Point) :
    canonicalPairing M P Q=canonicalPairing M Q P :=
  CanonicalQuadratic.pairing_symm (canonical_parallelogram M) P Q

theorem canonicalPairing_self (M : PrimitiveDynamics.Model)
    [(curve M.a M.b M.c).IsElliptic] (P : (curve M.a M.b M.c).Point) :
    canonicalPairing M P P=canonicalHeight M P :=
  CanonicalQuadratic.pairing_self (canonical_parallelogram M) P

/-- Integer quadraticity on the actual elliptic group, not an assumed height axiom. -/
theorem canonical_zsmul (M : PrimitiveDynamics.Model)
    [(curve M.a M.b M.c).IsElliptic] (n : ℤ) (P : (curve M.a M.b M.c).Point) :
    canonicalHeight M (n • P)=(n:ℝ)^2*canonicalHeight M P :=
  CanonicalQuadratic.map_zsmul (canonical_parallelogram M) n P

/-- Nonnegativity follows directly from the proved actual-group limit. -/
theorem canonical_nonneg (M : PrimitiveDynamics.Model) (P : (curve M.a M.b M.c).Point) :
    0 ≤ canonicalHeight M P := by
  apply ge_of_tendsto (tendsto_canonicalHeight M P)
  apply Filter.Eventually.of_forall
  intro n
  exact mul_nonneg (by positivity) (Height.logHeight_nonneg _)

/-- The exact finite Gram expansion used by the rational height certificates. -/
theorem canonical_sum_zsmul (M : PrimitiveDynamics.Model)
    [(curve M.a M.b M.c).IsElliptic] {ι : Type*} (s : Finset ι)
    (n : ι → ℤ) (P : ι → (curve M.a M.b M.c).Point) :
    canonicalHeight M (∑ i ∈ s, n i • P i)=
      ∑ i ∈ s, ∑ j ∈ s, (n i:ℝ)*(n j:ℝ)*canonicalPairing M (P i) (P j) := by
  rw [← canonicalPairing_self M]
  simp only [map_sum,map_zsmul,AddMonoidHom.finsetSum_apply,AddMonoidHom.zsmul_apply,zsmul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [canonicalPairing_symm M (P j) (P i)]
  ring


/-- Resolve the exact casted coefficients of the existing certified model. -/
instance branch1_2_model_isElliptic :
    (curve PrimitiveDynamics.branch1_2.a PrimitiveDynamics.branch1_2.b PrimitiveDynamics.branch1_2.c).IsElliptic := by
  change (curve (-1) (-65) (261)).IsElliptic
  infer_instance

/-- Resolve the exact casted coefficients of the existing certified model. -/
instance branch1_5_model_isElliptic :
    (curve PrimitiveDynamics.branch1_5.a PrimitiveDynamics.branch1_5.b PrimitiveDynamics.branch1_5.c).IsElliptic := by
  change (curve (-1) (-408) (6912)).IsElliptic
  infer_instance

/-- Resolve the exact casted coefficients of the existing certified model. -/
instance branch1_10_model_isElliptic :
    (curve PrimitiveDynamics.branch1_10.a PrimitiveDynamics.branch1_10.b PrimitiveDynamics.branch1_10.c).IsElliptic := by
  change (curve (1) (-1633) (97763)).IsElliptic
  infer_instance

/-- Resolve the exact casted coefficients of the existing certified model. -/
instance branch2_5_model_isElliptic :
    (curve PrimitiveDynamics.branch2_5.a PrimitiveDynamics.branch2_5.b PrimitiveDynamics.branch2_5.c).IsElliptic := by
  change (curve (1) (-1633) (32963)).IsElliptic
  infer_instance

/-- Concrete parallelogram endpoint with every model hypothesis discharged. -/
theorem branch1_2_parallelogram (P Q : (curve (-1) (-65) (261)).Point) :
    canonicalHeight PrimitiveDynamics.branch1_2 (P+Q)+canonicalHeight PrimitiveDynamics.branch1_2 (P-Q)=
      2*canonicalHeight PrimitiveDynamics.branch1_2 P+2*canonicalHeight PrimitiveDynamics.branch1_2 Q :=
  canonical_parallelogram PrimitiveDynamics.branch1_2 P Q

/-- Concrete quadraticity for every integer multiple, with no height premise. -/
theorem branch1_2_zsmul (n : ℤ) (P : (curve (-1) (-65) (261)).Point) :
    canonicalHeight PrimitiveDynamics.branch1_2 (n • P)=
      (n:ℝ)^2*canonicalHeight PrimitiveDynamics.branch1_2 P :=
  canonical_zsmul PrimitiveDynamics.branch1_2 n P

/-- Concrete parallelogram endpoint with every model hypothesis discharged. -/
theorem branch1_5_parallelogram (P Q : (curve (-1) (-408) (6912)).Point) :
    canonicalHeight PrimitiveDynamics.branch1_5 (P+Q)+canonicalHeight PrimitiveDynamics.branch1_5 (P-Q)=
      2*canonicalHeight PrimitiveDynamics.branch1_5 P+2*canonicalHeight PrimitiveDynamics.branch1_5 Q :=
  canonical_parallelogram PrimitiveDynamics.branch1_5 P Q

/-- Concrete quadraticity for every integer multiple, with no height premise. -/
theorem branch1_5_zsmul (n : ℤ) (P : (curve (-1) (-408) (6912)).Point) :
    canonicalHeight PrimitiveDynamics.branch1_5 (n • P)=
      (n:ℝ)^2*canonicalHeight PrimitiveDynamics.branch1_5 P :=
  canonical_zsmul PrimitiveDynamics.branch1_5 n P

/-- Concrete parallelogram endpoint with every model hypothesis discharged. -/
theorem branch1_10_parallelogram (P Q : (curve (1) (-1633) (97763)).Point) :
    canonicalHeight PrimitiveDynamics.branch1_10 (P+Q)+canonicalHeight PrimitiveDynamics.branch1_10 (P-Q)=
      2*canonicalHeight PrimitiveDynamics.branch1_10 P+2*canonicalHeight PrimitiveDynamics.branch1_10 Q :=
  canonical_parallelogram PrimitiveDynamics.branch1_10 P Q

/-- Concrete quadraticity for every integer multiple, with no height premise. -/
theorem branch1_10_zsmul (n : ℤ) (P : (curve (1) (-1633) (97763)).Point) :
    canonicalHeight PrimitiveDynamics.branch1_10 (n • P)=
      (n:ℝ)^2*canonicalHeight PrimitiveDynamics.branch1_10 P :=
  canonical_zsmul PrimitiveDynamics.branch1_10 n P

/-- Concrete parallelogram endpoint with every model hypothesis discharged. -/
theorem branch2_5_parallelogram (P Q : (curve (1) (-1633) (32963)).Point) :
    canonicalHeight PrimitiveDynamics.branch2_5 (P+Q)+canonicalHeight PrimitiveDynamics.branch2_5 (P-Q)=
      2*canonicalHeight PrimitiveDynamics.branch2_5 P+2*canonicalHeight PrimitiveDynamics.branch2_5 Q :=
  canonical_parallelogram PrimitiveDynamics.branch2_5 P Q

/-- Concrete quadraticity for every integer multiple, with no height premise. -/
theorem branch2_5_zsmul (n : ℤ) (P : (curve (1) (-1633) (32963)).Point) :
    canonicalHeight PrimitiveDynamics.branch2_5 (n • P)=
      (n:ℝ)^2*canonicalHeight PrimitiveDynamics.branch2_5 P :=
  canonical_zsmul PrimitiveDynamics.branch2_5 n P

end LcmSix.EllipticParallelogram
