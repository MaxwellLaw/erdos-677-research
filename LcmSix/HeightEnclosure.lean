/-
Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
-/
import LcmSix.EllipticDuplication

/-!
# Consuming finite-orbit logarithm certificates
This bridges the existing actual-group canonical-height tail to explicit
rational endpoints. The local rational-point gcd bound is not assumed:
32R≤D weakens the unconditional primitive-coordinate enclosure.
-/
namespace LcmSix.HeightEnclosure
open EllipticDuplication

/-- A seven-step actual group representative, three certified logarithm bounds
and two exact rounding inequalities enclose the actual canonical height. -/
theorem from_seven_steps (M : PrimitiveDynamics.Model)
    (P : (curve M.a M.b M.c).Point)
    (B D lB uB uC uD lo hi : ℝ)
    (hB : naiveHeight ((fun Q => Q+Q)^[7] P)=Real.log B)
    (hRD : 32*(M.R:ℝ)≤D)
    (hb : lB≤Real.log B ∧ Real.log B≤uB)
    (hc : Real.log M.C≤uC) (hd : Real.log D≤uD)
    (hl : lo≤(lB-uD/3)/16384) (hu : (uB+uC/3)/16384≤hi) :
    lo≤canonicalHeight M P ∧ canonicalHeight M P≤hi := by
  have hr : (0:ℝ)<32*(M.R:ℝ) := by
    have hp : (0:ℝ)<M.R := by exact_mod_cast M.R_pos
    positivity
  have hlogR : Real.log (32*(M.R:ℝ))≤uD := (Real.log_le_log hr hRD).trans hd
  have h := canonicalHeight_enclosure M P 7
  rw [hB] at h
  norm_num at h
  constructor <;> linarith

end LcmSix.HeightEnclosure
