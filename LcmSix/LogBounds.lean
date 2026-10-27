/-
Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Rational certificates for real logarithm enclosures

The analytic inequalities are the existing Mathlib theorems
`Real.sum_range_le_log_div` and `Real.log_div_le_sum_range_add`, from its
logarithm development credited to Chris Hughes, Abhimanyu Pallavi Sudhir,
Jean Lo and Calle Sönne. This module connects finite rational witnesses to
those real inequalities. In particular it uses Mathlib's wider remainder,
without the additional (2*n+1) denominator in the discovery script.
-/
namespace LcmSix.LogBounds

/-- The finite rational atanh series, including its factor two. -/
def lower (n : ℕ) (z : ℚ) : ℚ :=
  2 * ∑ i ∈ Finset.range n, z^(2*i+1)/(2*i+1)

/-- The remainder supplied by the pinned Mathlib inequality. -/
def upper (n : ℕ) (z : ℚ) : ℚ :=
  lower n z + 2*z^(2*n+1)/(1-z^2)

theorem lower_cast (n : ℕ) (z : ℚ) :
    (lower n z : ℝ)=2*∑ i ∈ Finset.range n, (z:ℝ)^(2*i+1)/(2*i+1) := by
  simp [lower]

/-- Exact rational inequalities suffice to enclose the actual real logarithm. -/
theorem ratio_log_bounds (n : ℕ) (z lo hi : ℚ)
    (hz : 0≤z) (hz1 : z<1)
    (hl : lo≤lower n z) (hu : upper n z≤hi) :
    (lo:ℝ)≤Real.log (((1+z)/(1-z):ℚ):ℝ) ∧
      Real.log (((1+z)/(1-z):ℚ):ℝ)≤hi := by
  have hzR : (0:ℝ)≤z := by exact_mod_cast hz
  have hz1R : (z:ℝ)<1 := by exact_mod_cast hz1
  have hlow := Real.sum_range_le_log_div hzR hz1R n
  have hupp := Real.log_div_le_sum_range_add hzR hz1R n
  have hlR : (lo:ℝ)≤(lower n z:ℝ) := by exact_mod_cast hl
  have huR : (upper n z:ℝ)≤(hi:ℝ) := by exact_mod_cast hu
  rw [lower_cast] at hlR
  simp only [upper,Rat.cast_add,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,
    Rat.cast_pow,Rat.cast_sub,Rat.cast_one,lower_cast] at huR
  rw [mul_div_assoc] at huR
  push_cast
  constructor <;> linarith

/-- A nonzero positive mantissa with a checked rational series parameter. -/
theorem mantissa_log_bounds (n : ℕ) (s z lo hi : ℚ)
    (hz : 0≤z) (hz1 : z<1) (hs : (1+z)/(1-z)=s)
    (hl : lo≤lower n z) (hu : upper n z≤hi) :
    (lo:ℝ)≤Real.log (s:ℝ) ∧ Real.log (s:ℝ)≤hi := by
  simpa only [hs] using ratio_log_bounds n z lo hi hz hz1 hl hu

/-- A natural-number cross product checks a large lower mantissa bracket. -/
theorem scaled_lower (N e p q : ℕ) (hq : 0<q) (h : 2^e*p≤N*q) :
    (2:ℚ)^e*((p:ℚ)/q)≤N := by
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by exact_mod_cast hq : (0:ℚ)<q)).mpr
  exact_mod_cast h

/-- A natural-number cross product checks a large upper mantissa bracket. -/
theorem scaled_upper (N e p q : ℕ) (hq : 0<q) (h : N*q≤2^e*p) :
    (N:ℚ)≤(2:ℚ)^e*((p:ℚ)/q) := by
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (by exact_mod_cast hq : (0:ℚ)<q)).mpr
  exact_mod_cast h

/-- Binary scaling and monotonicity transfer mantissa enclosures to a positive
integer. The binary exponent and rational bracket are explicit witnesses. -/
theorem integer_log_bounds (N e : ℕ) (slo shi l2 u2 llo uhi lo hi : ℚ)
    (hN : 0<N) (hsl : 0<slo)
    (hlo : (2:ℚ)^e*slo≤N) (hhi : (N:ℚ)≤(2:ℚ)^e*shi)
    (h2 : (l2:ℝ)≤Real.log 2 ∧ Real.log 2≤u2)
    (hl : (llo:ℝ)≤Real.log (slo:ℝ))
    (hu : Real.log (shi:ℝ)≤(uhi:ℝ))
    (hleft : lo≤(e:ℚ)*l2+llo) (hright : (e:ℚ)*u2+uhi≤hi) :
    (lo:ℝ)≤Real.log (N:ℝ) ∧ Real.log (N:ℝ)≤hi := by
  have hNR : (0:ℝ)<N := by exact_mod_cast hN
  have hslo : (0:ℝ)<slo := by exact_mod_cast hsl
  have hloR : (2:ℝ)^e*(slo:ℝ)≤N := by exact_mod_cast hlo
  have hhiR : (N:ℝ)≤(2:ℝ)^e*(shi:ℝ) := by exact_mod_cast hhi
  have hshi : (0:ℝ)<shi := by
    have := lt_of_lt_of_le hNR hhiR
    nlinarith [pow_pos (by norm_num : (0:ℝ)<2) e]
  have hlogl := Real.log_le_log (mul_pos (pow_pos (by norm_num : (0:ℝ)<2) e) hslo) hloR
  have hlogu := Real.log_le_log hNR hhiR
  rw [Real.log_mul (by positivity) hslo.ne',Real.log_pow] at hlogl
  rw [Real.log_mul (by positivity) hshi.ne',Real.log_pow] at hlogu
  have hlR : (lo:ℝ)≤(e:ℝ)*(l2:ℝ)+(llo:ℝ) := by exact_mod_cast hleft
  have huR : (e:ℝ)*(u2:ℝ)+(uhi:ℝ)≤hi := by exact_mod_cast hright
  have hm1 := mul_le_mul_of_nonneg_left h2.1 (Nat.cast_nonneg e : (0:ℝ)≤e)
  have hm2 := mul_le_mul_of_nonneg_left h2.2 (Nat.cast_nonneg e : (0:ℝ)≤e)
  constructor <;> linarith

end LcmSix.LogBounds
