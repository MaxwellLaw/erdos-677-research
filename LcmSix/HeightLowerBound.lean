/-
Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
-/
import LcmSix.HeightIntervals
import LcmSix.HeightGram

/-!
# Unconditional numerical height lower bounds on the four actual subgroups

Every orbit, logarithm, interval and matrix premise is discharged. This proves
independence and a height lower bound for the displayed triples. Full-group
generation and the complete length-six endpoint remain separate obligations.
-/
namespace LcmSix.HeightLowerBound
open EllipticDuplication

/-- The actual group canonical height vanishes at infinity. -/
theorem canonical_zero (M : PrimitiveDynamics.Model)
    [(curve M.a M.b M.c).IsElliptic] : canonicalHeight M 0=0 := by
  simpa using EllipticParallelogram.canonical_zsmul M 0 (0 : (curve M.a M.b M.c).Point)

/-- Positive squared-coefficient lower bounds exclude all nonzero relations. -/
theorem coefficients_zero (m : Fin 3 → ℤ)
    (h : (∑ i, (m i:ℝ)^2)/100≤0) : ∀ i, m i=0 := by
  simp only [Fin.sum_univ_three] at h
  have h0 : (m 0:ℝ)=0 := by nlinarith [sq_nonneg (m 1:ℝ),sq_nonneg (m 2:ℝ)]
  have h1 : (m 1:ℝ)=0 := by nlinarith [sq_nonneg (m 0:ℝ),sq_nonneg (m 2:ℝ)]
  have h2 : (m 2:ℝ)=0 := by nlinarith [sq_nonneg (m 0:ℝ),sq_nonneg (m 1:ℝ)]
  intro i
  fin_cases i
  · exact_mod_cast h0
  · exact_mod_cast h1
  · exact_mod_cast h2

/-- The actual displayed subgroup has the unconditional x-normalized bound. -/
theorem branch1_2_lower (m : Fin 3 → ℤ) :
    (∑ i, (m i:ℝ)^2)/100≤canonicalHeight PrimitiveDynamics.branch1_2
      (∑ i, m i • HeightGram.Branch1_2.basis i) :=
  HeightGram.Branch1_2.lower_of_intervals
    HeightIntervals.Branch1_2_P1_height HeightIntervals.Branch1_2_P2_height
    HeightIntervals.Branch1_2_P3_height HeightIntervals.Branch1_2_S12_height
    HeightIntervals.Branch1_2_S13_height HeightIntervals.Branch1_2_S23_height m

/-- No nontrivial integer relation among the actual three rational points. -/
theorem branch1_2_relation_trivial (m : Fin 3 → ℤ)
    (h : (∑ i, m i • HeightGram.Branch1_2.basis i)=0) : ∀ i, m i=0 := by
  have hb := branch1_2_lower m
  rw [h,canonical_zero] at hb
  exact coefficients_zero m hb

/-- The actual displayed subgroup has the unconditional x-normalized bound. -/
theorem branch1_5_lower (m : Fin 3 → ℤ) :
    (∑ i, (m i:ℝ)^2)/100≤canonicalHeight PrimitiveDynamics.branch1_5
      (∑ i, m i • HeightGram.Branch1_5.basis i) :=
  HeightGram.Branch1_5.lower_of_intervals
    HeightIntervals.Branch1_5_P1_height HeightIntervals.Branch1_5_P2_height
    HeightIntervals.Branch1_5_P3_height HeightIntervals.Branch1_5_S12_height
    HeightIntervals.Branch1_5_S13_height HeightIntervals.Branch1_5_S23_height m

/-- No nontrivial integer relation among the actual three rational points. -/
theorem branch1_5_relation_trivial (m : Fin 3 → ℤ)
    (h : (∑ i, m i • HeightGram.Branch1_5.basis i)=0) : ∀ i, m i=0 := by
  have hb := branch1_5_lower m
  rw [h,canonical_zero] at hb
  exact coefficients_zero m hb

/-- The actual displayed subgroup has the unconditional x-normalized bound. -/
theorem branch1_10_lower (m : Fin 3 → ℤ) :
    (∑ i, (m i:ℝ)^2)/100≤canonicalHeight PrimitiveDynamics.branch1_10
      (∑ i, m i • HeightGram.Branch1_10.basis i) :=
  HeightGram.Branch1_10.lower_of_intervals
    HeightIntervals.Branch1_10_P1_height HeightIntervals.Branch1_10_P2_height
    HeightIntervals.Branch1_10_P3_height HeightIntervals.Branch1_10_S12_height
    HeightIntervals.Branch1_10_S13_height HeightIntervals.Branch1_10_S23_height m

/-- No nontrivial integer relation among the actual three rational points. -/
theorem branch1_10_relation_trivial (m : Fin 3 → ℤ)
    (h : (∑ i, m i • HeightGram.Branch1_10.basis i)=0) : ∀ i, m i=0 := by
  have hb := branch1_10_lower m
  rw [h,canonical_zero] at hb
  exact coefficients_zero m hb

/-- The actual displayed subgroup has the unconditional x-normalized bound. -/
theorem branch2_5_lower (m : Fin 3 → ℤ) :
    (∑ i, (m i:ℝ)^2)/100≤canonicalHeight PrimitiveDynamics.branch2_5
      (∑ i, m i • HeightGram.Branch2_5.basis i) :=
  HeightGram.Branch2_5.lower_of_intervals
    HeightIntervals.Branch2_5_P1_height HeightIntervals.Branch2_5_P2_height
    HeightIntervals.Branch2_5_P3_height HeightIntervals.Branch2_5_S12_height
    HeightIntervals.Branch2_5_S13_height HeightIntervals.Branch2_5_S23_height m

/-- No nontrivial integer relation among the actual three rational points. -/
theorem branch2_5_relation_trivial (m : Fin 3 → ℤ)
    (h : (∑ i, m i • HeightGram.Branch2_5.basis i)=0) : ∀ i, m i=0 := by
  have hb := branch2_5_lower m
  rw [h,canonical_zero] at hb
  exact coefficients_zero m hb

end LcmSix.HeightLowerBound
