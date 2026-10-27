/-
Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Symmetric interval and rational sum-of-squares Gram certificates

All numerical premises are explicit. The height interpretation is supplied by
separate actual-point height intervals and the proved canonical pairing law.
No spectral or numerical-CAS assertion is imported as a premise.
-/

namespace LcmSix.GramBounds

/-- Six independent entries of a symmetric three by three matrix. -/
structure Sym3 where
  d1 : ℝ
  d2 : ℝ
  d3 : ℝ
  e12 : ℝ
  e13 : ℝ
  e23 : ℝ

def quad (q : Sym3) (x y z : ℝ) : ℝ :=
  q.d1*x^2+q.d2*y^2+q.d3*z^2+2*q.e12*x*y+2*q.e13*x*z+2*q.e23*y*z

/-- The pairing convention has diagonal H(P) and off-diagonal
(H(P+Q)-H(P)-H(Q))/2. -/
noncomputable def fromHeights (h1 h2 h3 h12 h13 h23 : ℝ) : Sym3 :=
  ⟨h1,h2,h3,(h12-h1-h2)/2,(h13-h1-h3)/2,(h23-h2-h3)/2⟩

/-- Symmetry is built into Sym3, so each off-diagonal radius is used twice. -/
def EntryBounds (q midpoint radius : Sym3) : Prop :=
  |q.d1-midpoint.d1| ≤ radius.d1 ∧
  |q.d2-midpoint.d2| ≤ radius.d2 ∧
  |q.d3-midpoint.d3| ≤ radius.d3 ∧
  |q.e12-midpoint.e12| ≤ radius.e12 ∧
  |q.e13-midpoint.e13| ≤ radius.e13 ∧
  |q.e23-midpoint.e23| ≤ radius.e23

lemma diagonal_error_lower {e r : ℝ} (he : |e| ≤ r) (x : ℝ) :
    -r*x^2 ≤ e*x^2 :=
  mul_le_mul_of_nonneg_right (abs_le.mp he).1 (sq_nonneg x)

lemma cross_error_lower {e r : ℝ} (he : |e| ≤ r) (x y : ℝ) :
    -r*(x^2+y^2) ≤ 2*e*x*y := by
  have hr : 0 ≤ r := (abs_nonneg e).trans he
  have hab : |e*(x*y)| ≤ r*|x*y| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right he (abs_nonneg _)
  have hl : -(r*|x*y|) ≤ e*(x*y) := (neg_le_neg hab).trans (neg_abs_le _)
  have hs : 2*|x*y| ≤ x^2+y^2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|x|-|y|),sq_abs x,sq_abs y]
  have hm := mul_le_mul_of_nonneg_left hs hr
  nlinarith

/-- A maximum row-radius bound controls the entire symmetric quadratic form. -/
theorem radius_lower (q midpoint radius : Sym3) (rho : ℝ)
    (hb : EntryBounds q midpoint radius)
    (hr1 : radius.d1+radius.e12+radius.e13 ≤ rho)
    (hr2 : radius.d2+radius.e12+radius.e23 ≤ rho)
    (hr3 : radius.d3+radius.e13+radius.e23 ≤ rho)
    (x y z : ℝ) :
    quad midpoint x y z-rho*(x^2+y^2+z^2) ≤ quad q x y z := by
  obtain ⟨h1,h2,h3,h12,h13,h23⟩ := hb
  have hd1 := diagonal_error_lower h1 x
  have hd2 := diagonal_error_lower h2 y
  have hd3 := diagonal_error_lower h3 z
  have he12 := cross_error_lower h12 x y
  have he13 := cross_error_lower h13 x z
  have he23 := cross_error_lower h23 y z
  have hm1 := mul_le_mul_of_nonneg_right hr1 (sq_nonneg x)
  have hm2 := mul_le_mul_of_nonneg_right hr2 (sq_nonneg y)
  have hm3 := mul_le_mul_of_nonneg_right hr3 (sq_nonneg z)
  unfold quad
  nlinarith only [hd1,hd2,hd3,he12,he13,he23,hm1,hm2,hm3]

/-- Completing-squares data; generated rational entries are checked in Lean. -/
structure SquareCertificate where
  d1 : ℝ
  d2 : ℝ
  d3 : ℝ
  l21 : ℝ
  l31 : ℝ
  l32 : ℝ

def SquareCertificate.Valid (s : SquareCertificate) (m : Sym3) (shift : ℝ) : Prop :=
  0 ≤ s.d1 ∧ 0 ≤ s.d2 ∧ 0 ≤ s.d3 ∧
  m.d1=shift+s.d1 ∧
  m.d2=shift+s.d1*s.l21^2+s.d2 ∧
  m.d3=shift+s.d1*s.l31^2+s.d2*s.l32^2+s.d3 ∧
  m.e12=s.d1*s.l21 ∧
  m.e13=s.d1*s.l31 ∧
  m.e23=s.d1*s.l21*s.l31+s.d2*s.l32

/-- The rational factorization is used as an exact polynomial identity. -/
theorem SquareCertificate.identity (s : SquareCertificate) (m : Sym3) (shift : ℝ)
    (hv : s.Valid m shift) (x y z : ℝ) :
    quad m x y z-shift*(x^2+y^2+z^2)=
      s.d1*(x+s.l21*y+s.l31*z)^2+s.d2*(y+s.l32*z)^2+s.d3*z^2 := by
  obtain ⟨_,_,_,h1,h2,h3,h12,h13,h23⟩ := hv
  simp only [quad,h1,h2,h3,h12,h13,h23]
  ring

/-- Positive semidefiniteness is proved by nonnegative squares, not by a CAS flag. -/
theorem SquareCertificate.lower (s : SquareCertificate) (m : Sym3) (shift : ℝ)
    (hv : s.Valid m shift) (x y z : ℝ) :
    shift*(x^2+y^2+z^2) ≤ quad m x y z := by
  have h := s.identity m shift hv x y z
  have h1 := mul_nonneg hv.1 (sq_nonneg (x+s.l21*y+s.l31*z))
  have h2 := mul_nonneg hv.2.1 (sq_nonneg (y+s.l32*z))
  have h3 := mul_nonneg hv.2.2.1 (sq_nonneg z)
  linarith

/-- Combine interval uncertainty with an exact completing-squares witness. -/
theorem certified_lower (q midpoint radius : Sym3) (rho lambda : ℝ)
    (s : SquareCertificate) (hv : s.Valid midpoint (lambda+rho))
    (hb : EntryBounds q midpoint radius)
    (hr1 : radius.d1+radius.e12+radius.e13 ≤ rho)
    (hr2 : radius.d2+radius.e12+radius.e23 ≤ rho)
    (hr3 : radius.d3+radius.e13+radius.e23 ≤ rho)
    (x y z : ℝ) :
    lambda*(x^2+y^2+z^2) ≤ quad q x y z := by
  have hm := s.lower midpoint (lambda+rho) hv x y z
  have he := radius_lower q midpoint radius rho hb hr1 hr2 hr3 x y z
  nlinarith only [hm,he]

/-- Expanded height form, directly consumable after the actual Gram identity. -/
theorem quad_fromHeights (h1 h2 h3 h12 h13 h23 x y z : ℝ) :
    quad (fromHeights h1 h2 h3 h12 h13 h23) x y z =
      h1*x^2+h2*y^2+h3*z^2+(h12-h1-h2)*x*y+
        (h13-h1-h3)*x*z+(h23-h2-h3)*y*z := by
  simp only [quad,fromHeights]
  ring

end LcmSix.GramBounds
