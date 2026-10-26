/-
Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
-/
import LcmSix.PrimitiveDynamics
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.NumberTheory.Height.NumberField

/-!
# The quartic map is actual elliptic-curve doubling

The proof uses Mathlib's nonsingular affine point group and its tangent formula
(by David Kurniadi Angdinata). The projective x-coordinate representative API
is from Mathlib. The projective-height API is due to Michael Stoll and
Ralf Stephan. No external group-law assertion or CAS equality is assumed.
The point at infinity and finite points doubled to infinity are included.
-/

namespace LcmSix.EllipticDuplication
open WeierstrassCurve Affine

/-- The exact integral-model shape used in all four length-six branches. -/
def curve (a b c : ℚ) : WeierstrassCurve.Affine ℚ := ⟨0,a,0,b,c⟩

def F (a b c p q : ℚ) : ℚ :=
  p^4-2*b*p^2*q^2-8*c*p*q^3+(b^2-4*a*c)*q^4

def G (a b c p q : ℚ) : ℚ :=
  4*(p^3*q+a*p^2*q^2+b*p*q^3+c*q^4)

theorem F_cast (a b c p q : ℤ) :
    F a b c p q = (HeightCertificates.F a b c p q : ℚ) := by
  simp only [F,HeightCertificates.F,HeightCertificates.homogeneousQuartic]
  push_cast
  ring

theorem G_cast (a b c p q : ℤ) :
    G a b c p q = (HeightCertificates.G a b c p q : ℚ) := by
  simp only [G,HeightCertificates.G,HeightCertificates.homogeneousQuartic]
  push_cast
  ring

theorem F_homogeneous (a b c p q r : ℚ) :
    F a b c (r*p) (r*q) = r^4*F a b c p q := by unfold F; ring

theorem G_homogeneous (a b c p q r : ℚ) :
    G a b c (r*p) (r*q) = r^4*G a b c p q := by unfold G; ring

theorem equation_iff (a b c x y : ℚ) :
    (curve a b c).Equation x y ↔ y^2=x^3+a*x^2+b*x+c := by
  simp [WeierstrassCurve.Affine.equation_iff,curve]

private theorem tangent_identity (a b c x y : ℚ)
    (he : y^2=x^3+a*x^2+b*x+c) (hy : y≠0) :
    F a b c x 1 = (4*y^2)*(((3*x^2+2*a*x+b)/(2*y))^2-a-x-x) := by
  unfold F
  field_simp
  linear_combination (norm := ring) 16*(a+2*x)*he

/-- The homogeneous quartic image of every actual point's x-representative is
an explicitly nonzero scalar multiple of the x-representative of its double. -/
theorem quartic_xRep_double (a b c : ℚ) (P : (curve a b c).Point) :
    ∃ s : ℚ, s≠0 ∧
      F a b c (P.xRep 0) (P.xRep 1)=s*(P+P).xRep 0 ∧
      G a b c (P.xRep 0) (P.xRep 1)=s*(P+P).xRep 1 := by
  cases P with
  | zero =>
    refine ⟨1,by norm_num,?_,?_⟩ <;> norm_num [← Point.zero_def,Point.xRep,F,G]
  | some x y hp =>
    have he := (equation_iff a b c x y).mp hp.1
    by_cases hy : y=0
    · have hneg : y=(curve a b c).negY x y := by simp [negY,curve,hy]
      have hd : (Point.some x y hp)+(Point.some x y hp)=0 := Point.add_self_of_Y_eq hneg
      have hder : 3*x^2+2*a*x+b≠0 := by
        have hn := (WeierstrassCurve.Affine.nonsingular_iff x y).mp hp
        simp only [curve,hy,zero_mul,neg_zero,sub_zero,ne_eq,not_true_eq_false,or_false] at hn
        exact Ne.symm hn.2
      refine ⟨(3*x^2+2*a*x+b)^2,pow_ne_zero _ hder,?_,?_⟩
      · rw [hd]
        simp only [Point.xRep_some,Point.xRep_zero,Matrix.cons_val_zero,Matrix.cons_val_one,
          Matrix.cons_val_fin_one,mul_one]
        unfold F
        subst y
        linear_combination (norm := ring) 4*(a+2*x)*he
      · rw [hd]
        simp only [Point.xRep_some,Point.xRep_zero,Matrix.cons_val_zero,Matrix.cons_val_one,
          Matrix.cons_val_fin_one,mul_zero]
        unfold G
        subst y
        linear_combination (norm := ring) -4*he
    · have hneg : y≠(curve a b c).negY x y := by
        simp only [negY,curve,zero_mul,sub_zero]
        intro h
        apply hy
        linarith
      have hd := Point.add_self_of_Y_ne (h₁:=hp) hneg
      have hs : (curve a b c).slope x x y y = (3*x^2+2*a*x+b)/(2*y) := by
        rw [slope_of_Y_ne rfl hneg]
        simp only [curve,negY,zero_mul,sub_zero]
        congr 1; ring
      refine ⟨4*y^2,mul_ne_zero (by norm_num) (pow_ne_zero _ hy),?_,?_⟩
      · rw [hd]
        simp only [Point.xRep_some,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
        rw [hs]
        simpa only [addX,curve,zero_mul,add_zero] using tangent_identity a b c x y he hy
      · rw [hd]
        simp only [Point.xRep_some,Matrix.cons_val_zero,Matrix.cons_val_one,
          Matrix.cons_val_fin_one,mul_one]
        unfold G
        linear_combination (norm := ring) -4*he


/-- A primitive integer pair represents the actual point's projective x-coordinate. -/
def Represents {a b c : ℚ} (P : (curve a b c).Point) (T : PrimitiveDynamics.Point) : Prop :=
  ∃ r : ℚ, r≠0 ∧ (T.p : ℚ)=r*P.xRep 0 ∧ (T.q : ℚ)=r*P.xRep 1

/-- The existing total primitive-coordinate map represents actual group doubling. -/
theorem step_represents (M : PrimitiveDynamics.Model)
    {P : (curve M.a M.b M.c).Point} {T : PrimitiveDynamics.Point}
    (hT : Represents P T) : Represents (P+P) (M.step T) := by
  obtain ⟨r,hr,hp,hq⟩ := hT
  obtain ⟨s,hs,hf,hg⟩ := quartic_xRep_double M.a M.b M.c P
  have hd : (M.divisor T : ℚ)≠0 := by exact_mod_cast (M.divisor_pos T).ne'
  refine ⟨r^4*s/(M.divisor T : ℚ),div_ne_zero (mul_ne_zero (pow_ne_zero _ hr) hs) hd,?_,?_⟩
  · have hv : (M.num T : ℚ)=r^4*s*(P+P).xRep 0 := by
      change (HeightCertificates.F M.a M.b M.c T.p T.q : ℚ)=_
      rw [← F_cast,hp,hq,F_homogeneous,hf]
      ring
    have he : ((M.step T).p : ℚ)*(M.divisor T : ℚ)=(M.num T : ℚ) := by
      exact_mod_cast Int.ediv_mul_cancel (Int.gcd_dvd_left (M.num T) (M.den T))
    calc
      _ = (M.num T : ℚ)/(M.divisor T : ℚ) := (eq_div_iff hd).mpr he
      _ = _ := by rw [hv]; ring
  · have hv : (M.den T : ℚ)=r^4*s*(P+P).xRep 1 := by
      change (HeightCertificates.G M.a M.b M.c T.p T.q : ℚ)=_
      rw [← G_cast,hp,hq,G_homogeneous,hg]
      ring
    have he : ((M.step T).q : ℚ)*(M.divisor T : ℚ)=(M.den T : ℚ) := by
      exact_mod_cast Int.ediv_mul_cancel (Int.gcd_dvd_right (M.num T) (M.den T))
    calc
      _ = (M.den T : ℚ)/(M.divisor T : ℚ) := (eq_div_iff hd).mpr he
      _ = _ := by rw [hv]; ring

/-- A canonical primitive representative: (1,0) at infinity, numerator and
positive denominator for an affine x-coordinate. -/
def primitiveRep {a b c : ℚ} : (curve a b c).Point → PrimitiveDynamics.Point
  | .zero => ⟨1,0,⟨1,0,by norm_num⟩⟩
  | .some x _ _ => ⟨x.num,x.den,x.isCoprime_num_den⟩

theorem primitiveRep_represents {a b c : ℚ} (P : (curve a b c).Point) :
    Represents P (primitiveRep P) := by
  cases P with
  | zero => refine ⟨1,by norm_num,?_,?_⟩ <;> norm_num [primitiveRep,Point.xRep]
  | some x y hp =>
    have hd : (x.den : ℚ)≠0 := by exact_mod_cast x.den_ne_zero
    refine ⟨x.den,hd,?_,?_⟩
    · change (x.num : ℚ)=(x.den : ℚ)*x
      simpa only [mul_comm] using (div_eq_iff hd).mp x.num_div_den
    · change ((x.den : ℤ) : ℚ)=(x.den : ℚ)*1
      norm_num

/-- The ordinary projective logarithmic x-height already defined in Mathlib. -/
noncomputable def naiveHeight {a b c : ℚ} (P : (curve a b c).Point) : ℝ :=
  Height.logHeight P.xRep

/-- Every primitive representative computes exactly the same naive height. -/
theorem height_eq_of_represents {a b c : ℚ} {P : (curve a b c).Point}
    {T : PrimitiveDynamics.Point} (hT : Represents P T) :
    PrimitiveDynamics.height T=naiveHeight P := by
  obtain ⟨r,hr,hp,hq⟩ := hT
  have hvec : ((Int.cast : ℤ → ℚ) ∘ ![T.p,T.q])=r • P.xRep := by
    ext i
    fin_cases i
    · simpa using hp
    · simpa using hq
  have hgcd : Finset.univ.gcd ![T.p,T.q]=1 := by
    simpa [Finset.univ_fin2,← Int.coe_gcd,← Int.abs_eq_normalize,Int.gcd_def,Int.natAbs_abs] using
      (show (Int.gcd T.p T.q : ℤ)=1 by exact_mod_cast Int.isCoprime_iff_gcd_eq_one.mp T.coprime)
  have ht := Rat.logHeight_eq_max_abs_of_gcd_eq_one hgcd
  rw [hvec,Height.logHeight_smul_eq_logHeight _ hr] at ht
  have hi : (⨆ i : Fin 2, |![T.p,T.q] i|)=max |T.p| |T.q| := by
    apply le_antisymm
    · apply ciSup_le
      intro i
      fin_cases i <;> simp
    · apply max_le
      · exact Finite.le_ciSup_of_le 0 (by simp)
      · exact Finite.le_ciSup_of_le 1 (by simp)
  rw [hi] at ht
  symm
  simpa only [naiveHeight,PrimitiveDynamics.height,PrimitiveDynamics.size,
    Int.cast_max,Int.cast_abs] using ht

/-- Compatibility persists along every group-doubling iterate. -/
theorem iterate_represents (M : PrimitiveDynamics.Model)
    {P : (curve M.a M.b M.c).Point} {T : PrimitiveDynamics.Point}
    (hT : Represents P T) (n : ℕ) :
    Represents ((fun Q : (curve M.a M.b M.c).Point => Q+Q)^[n] P) (M.step^[n] T) := by
  induction n with
  | zero => exact hT
  | succ n ih =>
    simpa only [Function.iterate_succ_apply'] using step_represents M ih


open Filter
open scoped Topology

/-- Canonical x-height, defined directly from the actual group-doubling orbit. -/
noncomputable def canonicalHeight (M : PrimitiveDynamics.Model)
    (P : (curve M.a M.b M.c).Point) : ℝ :=
  CanonicalLimit.canonical (fun Q => Q+Q) naiveHeight P

/-- Equality to the previously proved coordinate height, for any primitive representative. -/
theorem canonicalHeight_eq (M : PrimitiveDynamics.Model)
    {P : (curve M.a M.b M.c).Point} {T : PrimitiveDynamics.Point}
    (hT : Represents P T) : canonicalHeight M P=M.canonical T := by
  unfold canonicalHeight PrimitiveDynamics.Model.canonical CanonicalLimit.canonical
  congr 1
  funext n
  exact (height_eq_of_represents (iterate_represents M hT n)).symm

/-- Convergence for an actual rational elliptic-group point, including infinity. -/
theorem tendsto_canonicalHeight (M : PrimitiveDynamics.Model)
    (P : (curve M.a M.b M.c).Point) :
    Tendsto (fun n : ℕ => (1/4 : ℝ)^n *
      naiveHeight ((fun Q : (curve M.a M.b M.c).Point => Q+Q)^[n] P)) atTop
      (𝓝 (canonicalHeight M P)) := by
  have ht := M.tendsto_height (primitiveRep P)
  rw [← canonicalHeight_eq M (primitiveRep_represents P)] at ht
  convert ht using 1
  funext n
  rw [height_eq_of_represents (iterate_represents M (primitiveRep_represents P) n)]

/-- The actual group x-height has the certified one-step bounded defect. -/
theorem naiveHeight_defect (M : PrimitiveDynamics.Model)
    (P : (curve M.a M.b M.c).Point) :
    -Real.log (32*(M.R : ℝ)) ≤ naiveHeight (P+P)-4*naiveHeight P ∧
      naiveHeight (P+P)-4*naiveHeight P ≤ Real.log M.C := by
  have ht := M.height_defect (primitiveRep P)
  rw [height_eq_of_represents (step_represents M (primitiveRep_represents P)),
    height_eq_of_represents (primitiveRep_represents P)] at ht
  exact ht

/-- The defining canonical value scales under the actual elliptic group law. -/
theorem canonicalHeight_double (M : PrimitiveDynamics.Model)
    (P : (curve M.a M.b M.c).Point) :
    canonicalHeight M (P+P)=4*canonicalHeight M P := by
  have hb : ∀ Q : (curve M.a M.b M.c).Point,
      |naiveHeight (Q+Q)-4*naiveHeight Q| ≤ M.errorBound := by
    intro Q
    have h := M.abs_height_defect (primitiveRep Q)
    rw [height_eq_of_represents (step_represents M (primitiveRep_represents Q)),
      height_eq_of_represents (primitiveRep_represents Q)] at h
    exact h
  exact CanonicalLimit.canonical_map (fun Q => Q+Q) naiveHeight M.errorBound hb P

/-- Finite group-doubling iterates give explicit enclosures, with all points covered. -/
theorem canonicalHeight_enclosure (M : PrimitiveDynamics.Model)
    (P : (curve M.a M.b M.c).Point) (N : ℕ) :
    (1/4 : ℝ)^N * naiveHeight ((fun Q : (curve M.a M.b M.c).Point => Q+Q)^[N] P)
      -(1/4 : ℝ)^N*Real.log (32*(M.R : ℝ))/3 ≤ canonicalHeight M P ∧
    canonicalHeight M P ≤
      (1/4 : ℝ)^N * naiveHeight ((fun Q : (curve M.a M.b M.c).Point => Q+Q)^[N] P)
      +(1/4 : ℝ)^N*Real.log M.C/3 := by
  have h := M.canonical_enclosure (primitiveRep P) N
  rw [← canonicalHeight_eq M (primitiveRep_represents P),
    height_eq_of_represents (iterate_represents M (primitiveRep_represents P) N)] at h
  exact h

/-- The strict upper bound is now a theorem about the actual rational group. -/
theorem canonicalHeight_error_lt_five (M : PrimitiveDynamics.Model) (hC : M.C≤3061008)
    (P : (curve M.a M.b M.c).Point) : canonicalHeight M P-naiveHeight P<5 := by
  have h := M.height_error_lt_five hC (primitiveRep P)
  rw [← canonicalHeight_eq M (primitiveRep_represents P),
    height_eq_of_represents (primitiveRep_represents P)] at h
  exact h


/-- Repeated group doubling is multiplication by the exact natural power of two. -/
theorem double_iterate_eq_nsmul {A : Type*} [AddCommMonoid A] (P : A) (n : ℕ) :
    (fun Q : A => Q+Q)^[n] P=(2^n : ℕ) • P := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,← two_nsmul,smul_smul]
    congr 1
    ring

/-- The exact discriminant of this actual rational elliptic curve. -/
theorem branch1_2_discriminant : (curve (-1) (-65) (261)).Δ=(-6882048 : ℚ) := by
  norm_num [curve,WeierstrassCurve.Δ,WeierstrassCurve.b₂,
    WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]

instance branch1_2_isElliptic : (curve (-1) (-65) (261)).IsElliptic where
  isUnit := isUnit_iff_ne_zero.mpr (by rw [branch1_2_discriminant]; norm_num)

/-- Unconditional convergence for every rational point of the actual curve. -/
theorem branch1_2_group_converges (P : (curve (-1) (-65) (261)).Point) :
    Tendsto (fun n : ℕ => (1/4 : ℝ)^n * naiveHeight ((2^n : ℕ) • P))
      atTop (𝓝 (canonicalHeight PrimitiveDynamics.branch1_2 P)) := by
  convert tendsto_canonicalHeight PrimitiveDynamics.branch1_2 P using 1
  funext n
  exact congrArg (fun Q => (1/4 : ℝ)^n * naiveHeight Q)
    (double_iterate_eq_nsmul P n).symm

/-- The strict height bound, with no remaining model or representation premise. -/
theorem branch1_2_group_height_error (P : (curve (-1) (-65) (261)).Point) :
    canonicalHeight PrimitiveDynamics.branch1_2 P-naiveHeight P<5 :=
  canonicalHeight_error_lt_five PrimitiveDynamics.branch1_2
    (by norm_num [PrimitiveDynamics.branch1_2]) P

/-- The exact discriminant of this actual rational elliptic curve. -/
theorem branch1_5_discriminant : (curve (-1) (-408) (6912)).Δ=(-15477120000 : ℚ) := by
  norm_num [curve,WeierstrassCurve.Δ,WeierstrassCurve.b₂,
    WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]

instance branch1_5_isElliptic : (curve (-1) (-408) (6912)).IsElliptic where
  isUnit := isUnit_iff_ne_zero.mpr (by rw [branch1_5_discriminant]; norm_num)

/-- Unconditional convergence for every rational point of the actual curve. -/
theorem branch1_5_group_converges (P : (curve (-1) (-408) (6912)).Point) :
    Tendsto (fun n : ℕ => (1/4 : ℝ)^n * naiveHeight ((2^n : ℕ) • P))
      atTop (𝓝 (canonicalHeight PrimitiveDynamics.branch1_5 P)) := by
  convert tendsto_canonicalHeight PrimitiveDynamics.branch1_5 P using 1
  funext n
  exact congrArg (fun Q => (1/4 : ℝ)^n * naiveHeight Q)
    (double_iterate_eq_nsmul P n).symm

/-- The strict height bound, with no remaining model or representation premise. -/
theorem branch1_5_group_height_error (P : (curve (-1) (-408) (6912)).Point) :
    canonicalHeight PrimitiveDynamics.branch1_5 P-naiveHeight P<5 :=
  canonicalHeight_error_lt_five PrimitiveDynamics.branch1_5
    (by norm_num [PrimitiveDynamics.branch1_5]) P

/-- The exact discriminant of this actual rational elliptic curve. -/
theorem branch1_10_discriminant : (curve (1) (-1633) (97763)).Δ=(-3896125920000 : ℚ) := by
  norm_num [curve,WeierstrassCurve.Δ,WeierstrassCurve.b₂,
    WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]

instance branch1_10_isElliptic : (curve (1) (-1633) (97763)).IsElliptic where
  isUnit := isUnit_iff_ne_zero.mpr (by rw [branch1_10_discriminant]; norm_num)

/-- Unconditional convergence for every rational point of the actual curve. -/
theorem branch1_10_group_converges (P : (curve (1) (-1633) (97763)).Point) :
    Tendsto (fun n : ℕ => (1/4 : ℝ)^n * naiveHeight ((2^n : ℕ) • P))
      atTop (𝓝 (canonicalHeight PrimitiveDynamics.branch1_10 P)) := by
  convert tendsto_canonicalHeight PrimitiveDynamics.branch1_10 P using 1
  funext n
  exact congrArg (fun Q => (1/4 : ℝ)^n * naiveHeight Q)
    (double_iterate_eq_nsmul P n).symm

/-- The strict height bound, with no remaining model or representation premise. -/
theorem branch1_10_group_height_error (P : (curve (1) (-1633) (97763)).Point) :
    canonicalHeight PrimitiveDynamics.branch1_10 P-naiveHeight P<5 :=
  canonicalHeight_error_lt_five PrimitiveDynamics.branch1_10
    (by norm_num [PrimitiveDynamics.branch1_10]) P

/-- The exact discriminant of this actual rational elliptic curve. -/
theorem branch2_5_discriminant : (curve (1) (-1633) (32963)).Δ=(-206154720000 : ℚ) := by
  norm_num [curve,WeierstrassCurve.Δ,WeierstrassCurve.b₂,
    WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]

instance branch2_5_isElliptic : (curve (1) (-1633) (32963)).IsElliptic where
  isUnit := isUnit_iff_ne_zero.mpr (by rw [branch2_5_discriminant]; norm_num)

/-- Unconditional convergence for every rational point of the actual curve. -/
theorem branch2_5_group_converges (P : (curve (1) (-1633) (32963)).Point) :
    Tendsto (fun n : ℕ => (1/4 : ℝ)^n * naiveHeight ((2^n : ℕ) • P))
      atTop (𝓝 (canonicalHeight PrimitiveDynamics.branch2_5 P)) := by
  convert tendsto_canonicalHeight PrimitiveDynamics.branch2_5 P using 1
  funext n
  exact congrArg (fun Q => (1/4 : ℝ)^n * naiveHeight Q)
    (double_iterate_eq_nsmul P n).symm

/-- The strict height bound, with no remaining model or representation premise. -/
theorem branch2_5_group_height_error (P : (curve (1) (-1633) (32963)).Point) :
    canonicalHeight PrimitiveDynamics.branch2_5 P-naiveHeight P<5 :=
  canonicalHeight_error_lt_five PrimitiveDynamics.branch2_5
    (by norm_num [PrimitiveDynamics.branch2_5]) P

end LcmSix.EllipticDuplication
