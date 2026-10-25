/-
Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
Exact analytic inequalities for the coefficient bounds. The exponential is
bounded below by a finite Taylor sum whose arithmetic is checked by Lean;
no numerical approximation or external logarithm oracle is used.
-/

namespace LcmSix.HeightConstants

/-- The degree-ten Taylor partial sum at five already exceeds 146. -/
theorem exp_five_gt_146 : (146 : ℝ) < Real.exp 5 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 5) 11
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- Covers all four actual coefficient bounds with a strict uniform constant. -/
theorem log_C_div_three_lt_five {C : ℝ} (hC : 0 < C) (hmax : C ≤ 3061008) :
    Real.log C/3 < 5 := by
  have hpow : (146 : ℝ)^3 < (Real.exp 5)^3 :=
    pow_lt_pow_left₀ exp_five_gt_146 (by norm_num) (by norm_num)
  have h15 : (Real.exp 5)^3 = Real.exp 15 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hexp : C < Real.exp 15 := by
    rw [h15] at hpow
    norm_num at hpow
    linarith
  have hlog : Real.log C < 15 := (Real.log_lt_iff_lt_exp hC).mpr hexp
  linarith

end LcmSix.HeightConstants
