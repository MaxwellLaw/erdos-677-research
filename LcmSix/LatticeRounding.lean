/-
Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
-/
import LcmSix.LatticeDistance
import Mathlib.Data.Real.Basic

namespace LcmSix.LatticeDistance

theorem rounding_error_bound (m1 m2 m3 m0 e1 e2 e3 e0 eq B : ℝ)
    (hB : 0 ≤ B) (hm1 : |m1| ≤ B) (hm2 : |m2| ≤ B) (hm3 : |m3| ≤ B)
    (hm0 : |m0| ≤ 3*B+1)
    (h1 : |e1| ≤ 1/2) (h2 : |e2| ≤ 1/2) (h3 : |e3| ≤ 1/2)
    (h0 : |e0| ≤ 1/2) (hq : |eq| ≤ 1/2) :
    |m1*e1+m2*e2+m3*e3+m0*e0-eq| ≤ 3*B+1 := by
  have hp1 := mul_le_mul hm1 h1 (abs_nonneg e1) hB
  have hp2 := mul_le_mul hm2 h2 (abs_nonneg e2) hB
  have hp3 := mul_le_mul hm3 h3 (abs_nonneg e3) hB
  have hp0 := mul_le_mul hm0 h0 (abs_nonneg e0) (by linarith : 0 ≤ 3*B+1)
  rw [← abs_mul] at hp1 hp2 hp3 hp0
  have ha := abs_add_le (m1*e1) (m2*e2)
  have hb := abs_add_le (m1*e1+m2*e2) (m3*e3)
  have hc := abs_add_le (m1*e1+m2*e2+m3*e3) (m0*e0)
  have hd : |m1*e1+m2*e2+m3*e3+m0*e0-eq| ≤ |m1*e1+m2*e2+m3*e3+m0*e0|+|eq| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (m1*e1+m2*e2+m3*e3+m0*e0) (-eq)
  linarith

/-- Convert an integer distance certificate to a real linear-form lower bound.
The explicit hypotheses are rounding errors and coefficient bounds; no claim
about elliptic logarithms or the origin of those bounds is assumed. -/
theorem Certificate.real_linear_form_large (c : Certificate) (hc : c.Valid)
    (B K m1 m2 m3 m0 : ℤ) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hT : c.threshold = 3*B^2+(3*B+1+K)^2)
    (hm1 : |m1| ≤ B) (hm2 : |m2| ≤ B) (hm3 : |m3| ≤ B)
    (hm0 : |m0| ≤ 3*B+1)
    (C u1 u2 u3 omega uq : ℝ)
    (h1 : |(c.a1:ℝ)-C*u1| ≤ 1/2)
    (h2 : |(c.a2:ℝ)-C*u2| ≤ 1/2)
    (h3 : |(c.a3:ℝ)-C*u3| ≤ 1/2)
    (h0 : |(c.a0:ℝ)-C*omega| ≤ 1/2)
    (hq : |(c.target:ℝ)-C*uq| ≤ 1/2) :
    (K:ℝ) < |C*((m1:ℝ)*u1+(m2:ℝ)*u2+(m3:ℝ)*u3+(m0:ℝ)*omega-uq)| := by
  have hH : 0 ≤ 3*B+1+K := by omega
  have hg := c.last_coordinate_large hc B (3*B+1+K) m1 m2 m3 m0 hB hH hT hm1 hm2 hm3
  have hgR : (3*(B:ℝ)+1+(K:ℝ)) <
      |(c.a1:ℝ)*(m1:ℝ)+(c.a2:ℝ)*(m2:ℝ)+(c.a3:ℝ)*(m3:ℝ)+
        (c.a0:ℝ)*(m0:ℝ)-(c.target:ℝ)| := by exact_mod_cast hg
  have he := rounding_error_bound (m1:ℝ) (m2:ℝ) (m3:ℝ) (m0:ℝ)
    ((c.a1:ℝ)-C*u1) ((c.a2:ℝ)-C*u2) ((c.a3:ℝ)-C*u3)
    ((c.a0:ℝ)-C*omega) ((c.target:ℝ)-C*uq) (B:ℝ)
    (by exact_mod_cast hB) (by exact_mod_cast hm1) (by exact_mod_cast hm2)
    (by exact_mod_cast hm3) (by exact_mod_cast hm0) h1 h2 h3 h0 hq
  let z : ℝ := (c.a1:ℝ)*m1+(c.a2:ℝ)*m2+(c.a3:ℝ)*m3+(c.a0:ℝ)*m0-c.target
  let x : ℝ := C*((m1:ℝ)*u1+(m2:ℝ)*u2+(m3:ℝ)*u3+(m0:ℝ)*omega-uq)
  have heq : (m1:ℝ)*((c.a1:ℝ)-C*u1)+(m2:ℝ)*((c.a2:ℝ)-C*u2)+
      (m3:ℝ)*((c.a3:ℝ)-C*u3)+(m0:ℝ)*((c.a0:ℝ)-C*omega)-((c.target:ℝ)-C*uq) = z-x := by
    dsimp [z,x]; ring
  rw [heq] at he
  have ha : |z| ≤ |z-x|+|x| := by
    calc |z| = |(z-x)+x| := by ring_nf
         _ ≤ |z-x|+|x| := abs_add_le _ _
  change 3*(B:ℝ)+1+(K:ℝ) < |z| at hgR
  change (K:ℝ) < |x|
  linarith

end LcmSix.LatticeDistance
