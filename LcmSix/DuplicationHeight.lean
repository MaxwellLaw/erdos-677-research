/-
Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
-/
import LcmSix.DuplicationCertificates
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Polynomial size estimates and their logarithmic transfer. The explicit divisor
hypothesis is not a proof that a given integer is the actual gcd of the
coordinates of an elliptic-curve point. No rational-point or height theory is
assumed implicitly by these lemmas.
-/

namespace LcmSix.DuplicationBounds

def quartic (c0 c1 c2 c3 c4 p q : ℝ) : ℝ :=
  c0*p^4 + c1*p^3*q + c2*p^2*q^2 + c3*p*q^3 + c4*q^4

private theorem monomial_bound (c p q : ℝ) (i j : ℕ) (hij : i+j=4) :
    |c*p^i*q^j| ≤ |c| *(max |p| |q|)^4 := by
  have hm : 0 ≤ max |p| |q| := (abs_nonneg p).trans (le_max_left _ _)
  rw [abs_mul, abs_mul, abs_pow, abs_pow, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  calc
    |p|^i*|q|^j ≤ (max |p| |q|)^i*(max |p| |q|)^j :=
      mul_le_mul (pow_le_pow_left₀ (abs_nonneg p) (le_max_left _ _) i)
        (pow_le_pow_left₀ (abs_nonneg q) (le_max_right _ _) j)
        (pow_nonneg (abs_nonneg q) j) (pow_nonneg hm i)
    _ = (max |p| |q|)^4 := by rw [← pow_add, hij]

/-- The absolute coefficient sum bounds a homogeneous quartic on every real pair. -/
theorem quartic_upper (c0 c1 c2 c3 c4 p q : ℝ) :
    |quartic c0 c1 c2 c3 c4 p q| ≤
      (|c0|+|c1|+|c2|+|c3|+|c4|)*(max |p| |q|)^4 := by
  have h0 := monomial_bound c0 p q 4 0 (by norm_num)
  have h1 := monomial_bound c1 p q 3 1 (by norm_num)
  have h2 := monomial_bound c2 p q 2 2 (by norm_num)
  have h3 := monomial_bound c3 p q 1 3 (by norm_num)
  have h4 := monomial_bound c4 p q 0 4 (by norm_num)
  simp only [pow_zero, pow_one, mul_one] at h0 h1 h3 h4
  unfold quartic
  calc
    _ ≤ |c0*p^4+c1*p^3*q+c2*p^2*q^2+c3*p*q^3| + |c4*q^4| := abs_add_le _ _
    _ ≤ (|c0*p^4+c1*p^3*q+c2*p^2*q^2|+|c3*p*q^3|) + |c4*q^4| :=
      by linarith only [abs_add_le (c0*p^4+c1*p^3*q+c2*p^2*q^2) (c3*p*q^3)]
    _ ≤ ((|c0*p^4+c1*p^3*q|+|c2*p^2*q^2|)+|c3*p*q^3|) + |c4*q^4| :=
      by linarith only [abs_add_le (c0*p^4+c1*p^3*q) (c2*p^2*q^2)]
    _ ≤ (((|c0*p^4|+|c1*p^3*q|)+|c2*p^2*q^2|)+|c3*p*q^3|) + |c4*q^4| :=
      by linarith only [abs_add_le (c0*p^4) (c1*p^3*q)]
    _ ≤ (|c0|+|c1|+|c2|+|c3|+|c4|)*(max |p| |q|)^4 := by
      nlinarith only [h0,h1,h2,h3,h4]

/-- Maximum absolute coefficient sum of the two duplication quartics. -/
def coefficientBound (a b c : ℝ) : ℝ :=
  max (1 + |-2*b| + |-8*c| + |b^2-4*a*c|)
    (4 + |4*a| + |4*b| + |4*c|)

theorem pairNorm_upper (a b c p q : ℝ) :
    pairNorm a b c p q ≤ coefficientBound a b c*(max |p| |q|)^4 := by
  have hf := quartic_upper 1 0 (-2*b) (-8*c) (b^2-4*a*c) p q
  have hg := quartic_upper 0 4 (4*a) (4*b) (4*c) p q
  have hfeq : quartic 1 0 (-2*b) (-8*c) (b^2-4*a*c) p q = F a b c p q := by
    unfold quartic F
    ring
  have hgeq : quartic 0 4 (4*a) (4*b) (4*c) p q = G a b c p q := by
    unfold quartic G
    ring
  rw [hfeq] at hf
  rw [hgeq] at hg
  norm_num only [abs_zero, abs_one, show |(4 : ℝ)| = 4 by norm_num, zero_add, add_zero] at hf hg
  apply max_le
  · exact hf.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · exact hg.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

/-- A real lower/upper norm estimate gives a logarithmic duplication defect.
The divisor is supplied with its actual numerical bounds as explicit hypotheses. -/
theorem logarithmic_defect {a b c p q d D C : ℝ}
    (hpair : 0 < max |p| |q|) (hd : 1 ≤ d) (hdD : d ≤ D)
    (hC : 0 < C) (hupper : coefficientBound a b c ≤ C)
    (hlower : max |p| |q| ^ 4 ≤ 32*pairNorm a b c p q) :
    -Real.log (32*D) ≤
      Real.log (pairNorm a b c p q/d)-4*Real.log (max |p| |q|) ∧
    Real.log (pairNorm a b c p q/d)-4*Real.log (max |p| |q|) ≤ Real.log C := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hDpos : 0 < D := hdpos.trans_le hdD
  have hpow : 0 < max |p| |q| ^ 4 := pow_pos hpair 4
  have hnorm : 0 < pairNorm a b c p q := by nlinarith only [hpow,hlower]
  have hquot : 0 < pairNorm a b c p q/d := div_pos hnorm hdpos
  have hquotnorm : d*(pairNorm a b c p q/d) = pairNorm a b c p q :=
    mul_div_cancel₀ _ hdpos.ne'
  have hlow : max |p| |q| ^ 4 ≤ (32*D)*(pairNorm a b c p q/d) := by
    calc
      _ ≤ 32*pairNorm a b c p q := hlower
      _ = (32*d)*(pairNorm a b c p q/d) := by rw [mul_assoc,hquotnorm]
      _ ≤ (32*D)*(pairNorm a b c p q/d) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdD (by norm_num)) hquot.le
  have hup : pairNorm a b c p q/d ≤ C*(max |p| |q|)^4 := by
    calc
      _ ≤ pairNorm a b c p q := div_le_self hnorm.le hd
      _ ≤ coefficientBound a b c*(max |p| |q|)^4 := pairNorm_upper a b c p q
      _ ≤ C*(max |p| |q|)^4 := mul_le_mul_of_nonneg_right hupper hpow.le
  have hll := Real.log_le_log hpow hlow
  have hlu := Real.log_le_log hquot hup
  rw [Real.log_pow, Real.log_mul (mul_pos (by norm_num) hDpos).ne' hquot.ne'] at hll
  rw [Real.log_mul hC.ne' hpow.ne', Real.log_pow] at hlu
  norm_num only [Nat.cast_ofNat] at hll hlu
  constructor <;> linarith only [hll,hlu]

namespace Branch1_2

theorem coefficient_bound : coefficientBound (-1) (-65) 261 = 7488 := by
  norm_num [coefficientBound]

theorem defect_bounds {p q d : ℝ} (hpair : 0 < max |p| |q|)
    (hd : 1 ≤ d) (hdD : d ≤ 144) :
    -Real.log 4608 ≤ Real.log (pairNorm (-1) (-65) 261 p q/d)-4*Real.log (max |p| |q|) ∧
    Real.log (pairNorm (-1) (-65) 261 p q/d)-4*Real.log (max |p| |q|) ≤ Real.log 7488 := by
  have h := logarithmic_defect hpair hd hdD (by norm_num : (0 : ℝ) < 7488)
    (le_of_eq coefficient_bound) (global_lower p q)
  norm_num only [show (32 : ℝ)*144=4608 by norm_num] at h
  exact h

end Branch1_2

namespace Branch1_5

theorem coefficient_bound : coefficientBound (-1) (-408) 6912 = 250225 := by
  norm_num [coefficientBound]

theorem defect_bounds {p q d : ℝ} (hpair : 0 < max |p| |q|)
    (hd : 1 ≤ d) (hdD : d ≤ 14400) :
    -Real.log 460800 ≤ Real.log (pairNorm (-1) (-408) 6912 p q/d)-4*Real.log (max |p| |q|) ∧
    Real.log (pairNorm (-1) (-408) 6912 p q/d)-4*Real.log (max |p| |q|) ≤ Real.log 250225 := by
  have h := logarithmic_defect hpair hd hdD (by norm_num : (0 : ℝ) < 250225)
    (le_of_eq coefficient_bound) (global_lower p q)
  norm_num only [show (32 : ℝ)*14400=460800 by norm_num] at h
  exact h

end Branch1_5

namespace Branch1_10

theorem coefficient_bound : coefficientBound 1 (-1633) 97763 = 3061008 := by
  norm_num [coefficientBound]

theorem defect_bounds {p q d : ℝ} (hpair : 0 < max |p| |q|)
    (hd : 1 ≤ d) (hdD : d ≤ 291600) :
    -Real.log 9331200 ≤ Real.log (pairNorm 1 (-1633) 97763 p q/d)-4*Real.log (max |p| |q|) ∧
    Real.log (pairNorm 1 (-1633) 97763 p q/d)-4*Real.log (max |p| |q|) ≤ Real.log 3061008 := by
  have h := logarithmic_defect hpair hd hdD (by norm_num : (0 : ℝ) < 3061008)
    (le_of_eq coefficient_bound) (global_lower p q)
  norm_num only [show (32 : ℝ)*291600=9331200 by norm_num] at h
  exact h

end Branch1_10

namespace Branch2_5

theorem coefficient_bound : coefficientBound 1 (-1633) 32963 = 2801808 := by
  norm_num [coefficientBound]

theorem defect_bounds {p q d : ℝ} (hpair : 0 < max |p| |q|)
    (hd : 1 ≤ d) (hdD : d ≤ 32400) :
    -Real.log 1036800 ≤ Real.log (pairNorm 1 (-1633) 32963 p q/d)-4*Real.log (max |p| |q|) ∧
    Real.log (pairNorm 1 (-1633) 32963 p q/d)-4*Real.log (max |p| |q|) ≤ Real.log 2801808 := by
  have h := logarithmic_defect hpair hd hdD (by norm_num : (0 : ℝ) < 2801808)
    (le_of_eq coefficient_bound) (global_lower p q)
  norm_num only [show (32 : ℝ)*32400=1036800 by norm_num] at h
  exact h

end Branch2_5

end LcmSix.DuplicationBounds
