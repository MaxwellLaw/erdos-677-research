import Mathlib.Tactic.Ring

/-!
# A centered common-divisor obstruction for the length-six reduction

The polynomial identity
`Phi T + 225 = T * (T^2 - 35*T + 259)`
shows that a common divisor `d` of `X` and `Y` has its square dividing
both `Phi (X^2) + 225` and `Phi (Y^2) + 225`.  Taking the indicated
linear combination of these two divisibilities yields the constant obstruction.

This formalizes an elementary necessary condition in the centered-curve
reduction.  It does not solve the curves, prove the reduction from LCMs,
or prove the length-six noncollision theorem.
-/

namespace LcmSixGcd

/-- The cubic used for the centered product of six consecutive integers. -/
def Phi (T : ℤ) : ℤ := (T - 1) * (T - 9) * (T - 25)

/-- The constant term is `-225`; every other term contains `T`. -/
theorem phi_add_225 (T : ℤ) :
    Phi T + 225 = T * (T ^ 2 - 35 * T + 259) := by
  unfold Phi
  ring

/-- Squaring a divisor of the centered coordinate divides the adjusted cubic. -/
theorem square_dvd_phi_square_add_225 {d X : ℤ} (hX : d ∣ X) :
    d ^ 2 ∣ Phi (X ^ 2) + 225 := by
  rcases hX with ⟨q, rfl⟩
  refine ⟨q ^ 2 * ((d * q) ^ 4 - 35 * (d * q) ^ 2 + 259), ?_⟩
  rw [phi_add_225]
  ring

/--
A necessary divisibility condition for an integer point on a centered ratio
curve.  The statement covers all integer coefficients and all common divisors,
including zero and negative values, without division or exceptional cases.
-/
theorem common_divisor_square_dvd
    {a b X Y d : ℤ}
    (hcurve : a * Phi (Y ^ 2) = b * Phi (X ^ 2))
    (hX : d ∣ X) (hY : d ∣ Y) :
    d ^ 2 ∣ 225 * (b - a) := by
  have hx := square_dvd_phi_square_add_225 hX
  have hy := square_dvd_phi_square_add_225 hY
  have hlin : d ^ 2 ∣ b * (Phi (X ^ 2) + 225) - a * (Phi (Y ^ 2) + 225) :=
    Int.dvd_sub (dvd_mul_of_dvd_right hx b) (dvd_mul_of_dvd_right hy a)
  have heq :
      b * (Phi (X ^ 2) + 225) - a * (Phi (Y ^ 2) + 225) = 225 * (b - a) := by
    calc
      b * (Phi (X ^ 2) + 225) - a * (Phi (Y ^ 2) + 225) =
          (b * Phi (X ^ 2) - a * Phi (Y ^ 2)) + 225 * (b - a) := by ring
      _ = 225 * (b - a) := by rw [hcurve]; ring
  rwa [heq] at hlin

end LcmSixGcd
