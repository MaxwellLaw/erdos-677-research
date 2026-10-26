/-
Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
-/
import LcmSix.EllipticDuplication
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap

/-!
# The actual addition-and-subtraction identity for rational cubic models

Mathlib's addSubMap and sym2x definitions and polynomial certificates are due
to Michael Stoll; the affine group law and formulae are due to David Kurniadi
Angdinata. This file supplies compatibility with that actual group law for
the project's pinned Mathlib version, including all points at infinity and
equal-x exceptional cases. Mathlib main already has Stoll's more general
identity (commit 69fe4f49ffbc9580a2c3ae6d29591ef6d1d4131e); no first-formalization
claim is made here. No CAS
assertion or unproved map identity is used.
-/

namespace LcmSix.EllipticAddSub
open WeierstrassCurve Affine
open EllipticDuplication

/-- Evaluation of the existing Mathlib polynomial map, not a replacement map. -/
noncomputable def evalMap (a b c : ℚ) (v : Fin 3 → ℚ) : Fin 3 → ℚ :=
  fun i => ((curve a b c).addSubMap i).eval v

/-- Expanded evaluation of the short-model coefficients. -/
theorem evalMap_formula (a b c s t u : ℚ) :
    evalMap a b c ![s,t,u]=
      ![s^2-2*b*s*u-4*c*t*u-(4*a*c-b^2)*u^2,
        2*t*s+4*a*s*u+2*b*t*u+4*c*u^2,t^2-4*s*u] := by
  ext i
  fin_cases i <;>
    simp [evalMap,WeierstrassCurve.addSubMap,curve,WeierstrassCurve.b₂,
      WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]

/-- The polynomial map on the diagonal is exactly the quartic duplication pair. -/
theorem evalMap_diagonal (a b c p q : ℚ) :
    evalMap a b c ![p*p,p*q+q*p,q*q]=![F a b c p q,G a b c p q,0] := by
  rw [evalMap_formula]
  ext i
  fin_cases i <;> simp [F,G] <;> ring

private theorem chord_product_identity (a b c x z y w : ℚ)
    (hy : y^2=x^3+a*x^2+b*x+c) (hw : w^2=z^3+a*z^2+b*z+c) :
    (y^2+w^2-(a+x+z)*(x-z)^2)^2-4*y^2*w^2 =
      ((x*z)^2-2*b*x*z-4*c*(x+z)-(4*a*c-b^2))*(x-z)^2 := by
  rw [hy,hw]
  ring

private theorem chord_sum_identity (a b c x z y w : ℚ)
    (hy : y^2=x^3+a*x^2+b*x+c) (hw : w^2=z^3+a*z^2+b*z+c) :
    2*(y^2+w^2-(a+x+z)*(x-z)^2)=
      2*(x+z)*(x*z)+4*a*(x*z)+2*b*(x+z)+4*c := by
  rw [hy,hw]
  ring

private theorem chord_product (a b c x z y w : ℚ) (hx : x≠z)
    (hy : y^2=x^3+a*x^2+b*x+c) (hw : w^2=z^3+a*z^2+b*z+c) :
    (x*z)^2-2*b*(x*z)-4*c*(x+z)-(4*a*c-b^2) =
      (x-z)^2*(((y-w)/(x-z))^2-a-x-z)*(((y+w)/(x-z))^2-a-x-z) := by
  have hd : x-z≠0 := sub_ne_zero.mpr hx
  have hp := chord_product_identity a b c x z y w hy hw
  field_simp
  linear_combination (norm := ring) -hp

private theorem chord_sum (a b c x z y w : ℚ) (hx : x≠z)
    (hy : y^2=x^3+a*x^2+b*x+c) (hw : w^2=z^3+a*z^2+b*z+c) :
    2*(x+z)*(x*z)+4*a*(x*z)+2*b*(x+z)+4*c =
      (x-z)^2*((((y-w)/(x-z))^2-a-x-z)+(((y+w)/(x-z))^2-a-x-z)) := by
  have hd : x-z≠0 := sub_ne_zero.mpr hx
  have hp := chord_sum_identity a b c x z y w hy hw
  field_simp
  linear_combination (norm := ring) -hp

/-- The equal-point case includes points of order two and infinity. -/
theorem diagonal (a b c : ℚ) (P : (curve a b c).Point) :
    ∃ r : ℚ, r≠0 ∧ evalMap a b c (P.sym2x P)=r • (P+P).sym2x (P-P) := by
  obtain ⟨r,hr,hf,hg⟩ := quartic_xRep_double a b c P
  refine ⟨r,hr,?_⟩
  rw [sub_self]
  change evalMap a b c ![P.xRep 0*P.xRep 0,
    P.xRep 0*P.xRep 1+P.xRep 1*P.xRep 0,P.xRep 1*P.xRep 1]=_
  rw [evalMap_diagonal]
  ext i
  fin_cases i <;> simp [Point.sym2x,hf,hg]

/-- Replacing the second input by its negative exchanges sum and difference. -/
theorem antidiagonal (a b c : ℚ) (P : (curve a b c).Point) :
    ∃ r : ℚ, r≠0 ∧ evalMap a b c (P.sym2x (-P))=r • (P+(-P)).sym2x (P-(-P)) := by
  obtain ⟨r,hr,h⟩ := diagonal a b c P
  refine ⟨r,hr,?_⟩
  simpa only [Point.sym2x_neg_right,sub_neg_eq_add,add_neg_cancel,sub_self,
    Point.sym2x_comm (0 : (curve a b c).Point)] using h

/-- Infinity in the first input has scalar one. -/
theorem zero_left (a b c : ℚ) (Q : (curve a b c).Point) :
    evalMap a b c ((0 : (curve a b c).Point).sym2x Q)=(0+Q).sym2x (0-Q) := by
  simp only [zero_add,zero_sub,Point.sym2x_neg_right]
  simp only [Point.sym2x,Point.xRep_zero,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,one_mul,zero_mul,add_zero]
  rw [evalMap_formula]
  ext i
  fin_cases i <;> simp <;> ring

/-- Infinity in the second input has scalar one. -/
theorem zero_right (a b c : ℚ) (P : (curve a b c).Point) :
    evalMap a b c (P.sym2x (0 : (curve a b c).Point))=(P+0).sym2x (P-0) := by
  simpa only [Point.sym2x_comm P 0,zero_add,zero_sub,add_zero,sub_zero,
    Point.sym2x_neg_right] using zero_left a b c P

/-- The chord case uses the nonzero square of the x-coordinate difference. -/
theorem distinct_x (a b c x z y w : ℚ)
    (hp : (curve a b c).Nonsingular x y) (hq : (curve a b c).Nonsingular z w)
    (hx : x≠z) :
    evalMap a b c ((Point.some x y hp).sym2x (Point.some z w hq))=
      (x-z)^2 • ((Point.some x y hp)+(Point.some z w hq)).sym2x
        ((Point.some x y hp)-(Point.some z w hq)) := by
  have hy := (EllipticDuplication.equation_iff a b c x y).mp hp.1
  have hw := (EllipticDuplication.equation_iff a b c z w).mp hq.1
  have hsub : (Point.some x y hp)-(Point.some z w hq) =
      (Point.some x y hp)+(-(Point.some z w hq)) := sub_eq_add_neg _ _
  rw [Point.sym2x_some_some,evalMap_formula,hsub,Point.neg_some,
    Point.add_of_X_ne hx,Point.add_of_X_ne hx,Point.sym2x_some_some]
  simp only [slope_of_X_ne hx,addX,negY,curve,zero_mul,sub_zero,add_zero,sub_neg_eq_add]
  ext i
  fin_cases i
  · simpa [mul_assoc] using chord_product a b c x z y w hx hy hw
  · simpa using chord_sum a b c x z y w hx hy hw
  · simp
    ring

/-- Full projective compatibility with actual group addition and subtraction.
There are no excluded infinity, two-torsion or equal-x input pairs. -/
theorem addSubMap_sym2x (a b c : ℚ) (P Q : (curve a b c).Point) :
    ∃ r : ℚ, r≠0 ∧
      (fun i : Fin 3 => ((curve a b c).addSubMap i).eval (P.sym2x Q))=
        r • (P+Q).sym2x (P-Q) := by
  change ∃ r : ℚ, r≠0 ∧ evalMap a b c (P.sym2x Q)=r • (P+Q).sym2x (P-Q)
  cases P with
  | zero =>
    refine ⟨1,by norm_num,?_⟩
    simpa only [← Point.zero_def,one_smul] using zero_left a b c Q
  | some x y hp =>
    cases Q with
    | zero =>
      refine ⟨1,by norm_num,?_⟩
      simpa only [← Point.zero_def,one_smul] using zero_right a b c (Point.some x y hp)
    | some z w hq =>
      by_cases hx : x=z
      · obtain h | h := (Point.X_eq_iff (h₁:=hp) (h₂:=hq)).mp hx
        · rw [h]
          exact diagonal a b c (Point.some z w hq)
        · have he : Point.some z w hq = -(Point.some x y hp) := by rw [h]; exact (neg_neg _).symm
          rw [he]
          exact antidiagonal a b c (Point.some x y hp)
      · exact ⟨(x-z)^2,pow_ne_zero _ (sub_ne_zero.mpr hx),distinct_x a b c x z y w hp hq hx⟩

end LcmSix.EllipticAddSub
