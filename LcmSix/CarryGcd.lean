/- Copyright (c) 2026 MaxwellLaw. Released under Apache 2.0. -/
import LcmSix.Reduction
import LcmSix.GcdBound
import Mathlib.Data.Int.GCD

/-!
# Carry-refined common-divisor constraints

These are length-six specializations of the centered gcd obstruction and the
slope gcd relation. They retain the exact carry condition. They do not prove
that the branches are empty. The general gcd relations are prior results in
Danesh--Bianchetti, Proposition 25; the small constants here are explicit
consequences of those relations and the length-six carry formula.
-/

namespace LcmSix

def centerGcd (n m : ℕ) : ℕ := Int.gcd (center n) (center m)

def slopeGcd (n m a b : ℕ) : ℕ :=
  Int.gcd ((b : ℤ) * center n - (a : ℤ) * center m) (center m - center n)

/-- The centered gcd is odd, regardless of the curve equation. -/
lemma centerGcd_not_two_dvd (n m : ℕ) : ¬ 2 ∣ centerGcd n m := by
  intro h
  have hz : (2 : ℤ) ∣ (centerGcd n m : ℤ) := by exact_mod_cast h
  have hx := dvd_trans hz (Int.gcd_dvd_left (center n) (center m))
  rcases hx with ⟨q, hq⟩
  dsimp [center] at hq
  omega

lemma centerGcd_not_five_dvd {n m : ℕ} (hn : n % 5 ≠ 4) :
    ¬ 5 ∣ centerGcd n m := by
  intro h
  have hz : (5 : ℤ) ∣ (centerGcd n m : ℤ) := by exact_mod_cast h
  have hx := dvd_trans hz (Int.gcd_dvd_left (center n) (center m))
  rcases hx with ⟨q, hq⟩
  dsimp [center] at hq
  omega

/-- In the last three coefficient branches the first carry has no factor 5. -/
lemma first_residue_ne_four {n m a b : ℕ}
    (hab : (a = 1 ∧ b = 5) ∨ (a = 1 ∧ b = 10) ∨ (a = 2 ∧ b = 5))
    (h : a * carry m = b * carry n) : n % 5 ≠ 4 := by
  intro hn
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    unfold carry at h <;>
    simp only [hn, if_pos] at h <;>
    split_ifs at h <;> norm_num at h

lemma centerGcd_square_dvd {n m a b : ℕ} (h : CurveBranch n m a b) :
    (centerGcd n m : ℤ) ^ 2 ∣ 225 * ((b : ℤ) - (a : ℤ)) := by
  have hcurve :
      (a : ℤ) * LcmSixGcd.Phi (center m ^ 2) =
        (b : ℤ) * LcmSixGcd.Phi (center n ^ 2) := by
    simpa only [LcmSixGcd.Phi, Phi] using h.2
  exact LcmSixGcd.common_divisor_square_dvd hcurve
    (Int.gcd_dvd_left (center n) (center m))
    (Int.gcd_dvd_right (center n) (center m))

/-- The coefficient-(1,2) branch has centered gcd dividing 15. -/
theorem centerGcd_dvd_15_of_branch_1_2 {n m : ℕ} (h : CurveBranch n m 1 2) :
    centerGcd n m ∣ 15 := by
  have hz := centerGcd_square_dvd h
  norm_num at hz
  have hs : centerGcd n m ^ 2 ∣ 225 := by exact_mod_cast hz
  have hle := Nat.le_of_dvd (by decide : 0 < 225) hs
  have hb : centerGcd n m ≤ 15 := by nlinarith
  interval_cases hd : centerGcd n m <;> norm_num [hd] at hs <;> norm_num [hd]

/-- Exact carry conditions remove factor 5; odd centers remove factor 2. -/
theorem centerGcd_dvd_3_of_branch_1_5 {n m : ℕ} (h : CurveBranch n m 1 5) :
    centerGcd n m ∣ 3 := by
  have hz := centerGcd_square_dvd h
  norm_num at hz
  have hs : centerGcd n m ^ 2 ∣ 900 := by exact_mod_cast hz
  have h2 := centerGcd_not_two_dvd n m
  have h5 := centerGcd_not_five_dvd (m := m)
    (first_residue_ne_four (Or.inl ⟨rfl, rfl⟩) h.1)
  have hle := Nat.le_of_dvd (by decide : 0 < 900) hs
  have hb : centerGcd n m ≤ 30 := by nlinarith
  interval_cases hd : centerGcd n m <;> norm_num [hd] at hs <;>
    norm_num [hd] at h2 <;> norm_num [hd] at h5 <;> norm_num [hd]

theorem centerGcd_dvd_9_of_branch_1_10 {n m : ℕ} (h : CurveBranch n m 1 10) :
    centerGcd n m ∣ 9 := by
  have hz := centerGcd_square_dvd h
  norm_num at hz
  have hs : centerGcd n m ^ 2 ∣ 2025 := by exact_mod_cast hz
  have h5 := centerGcd_not_five_dvd (m := m)
    (first_residue_ne_four (Or.inr (Or.inl ⟨rfl, rfl⟩)) h.1)
  have hle := Nat.le_of_dvd (by decide : 0 < 2025) hs
  have hb : centerGcd n m ≤ 45 := by nlinarith
  interval_cases hd : centerGcd n m <;> norm_num [hd] at hs <;>
    norm_num [hd] at h5 <;> norm_num [hd]

theorem centerGcd_dvd_3_of_branch_2_5 {n m : ℕ} (h : CurveBranch n m 2 5) :
    centerGcd n m ∣ 3 := by
  have hz := centerGcd_square_dvd h
  norm_num at hz
  have hs : centerGcd n m ^ 2 ∣ 675 := by exact_mod_cast hz
  have h5 := centerGcd_not_five_dvd (m := m)
    (first_residue_ne_four (Or.inr (Or.inr ⟨rfl, rfl⟩)) h.1)
  have hle := Nat.le_of_dvd (by decide : 0 < 675) hs
  have hb : centerGcd n m ≤ 25 := by nlinarith
  interval_cases hd : centerGcd n m <;> norm_num [hd] at hs <;>
    norm_num [hd] at h5 <;> norm_num [hd]

/-- The general slope gcd relation, valid for all integers without division. -/
theorem slope_gcd_dvd_difference_mul_gcd (a b X Y : ℤ) :
    (Int.gcd (b * X - a * Y) (Y - X) : ℤ) ∣
      (b - a) * (Int.gcd X Y : ℤ) := by
  have hr := Int.gcd_dvd_left (b * X - a * Y) (Y - X)
  have hs := Int.gcd_dvd_right (b * X - a * Y) (Y - X)
  have hx : (Int.gcd (b * X - a * Y) (Y - X) : ℤ) ∣ (b - a) * X := by
    convert Int.dvd_add hr (dvd_mul_of_dvd_right hs a) using 1; ring
  have hy : (Int.gcd (b * X - a * Y) (Y - X) : ℤ) ∣ (b - a) * Y := by
    convert Int.dvd_add hr (dvd_mul_of_dvd_right hs b) using 1; ring
  rw [Int.gcd_eq_gcd_ab X Y]
  convert Int.dvd_add (dvd_mul_of_dvd_left hx (Int.gcdA X Y))
    (dvd_mul_of_dvd_left hy (Int.gcdB X Y)) using 1; ring

lemma slopeGcd_dvd_difference_mul_centerGcd (n m a b : ℕ) (hab : a ≤ b) :
    slopeGcd n m a b ∣ (b - a) * centerGcd n m := by
  have h := slope_gcd_dvd_difference_mul_gcd (a : ℤ) (b : ℤ) (center n) (center m)
  have h' : (slopeGcd n m a b : ℤ) ∣ (((b-a) * centerGcd n m : ℕ) : ℤ) := by
    simpa only [slopeGcd, centerGcd, Nat.cast_mul, Nat.cast_sub hab] using h
  exact_mod_cast h'

theorem slopeGcd_dvd_15_of_branch_1_2 {n m : ℕ} (h : CurveBranch n m 1 2) :
    slopeGcd n m 1 2 ∣ 15 := by
  have hs := slopeGcd_dvd_difference_mul_centerGcd n m 1 2 (by decide)
  norm_num at hs
  exact dvd_trans hs (centerGcd_dvd_15_of_branch_1_2 h)

theorem slopeGcd_dvd_12_of_branch_1_5 {n m : ℕ} (h : CurveBranch n m 1 5) :
    slopeGcd n m 1 5 ∣ 12 := by
  have hs := slopeGcd_dvd_difference_mul_centerGcd n m 1 5 (by decide)
  exact dvd_trans hs (Nat.mul_dvd_mul_left 4 (centerGcd_dvd_3_of_branch_1_5 h))

theorem slopeGcd_dvd_81_of_branch_1_10 {n m : ℕ} (h : CurveBranch n m 1 10) :
    slopeGcd n m 1 10 ∣ 81 := by
  have hs := slopeGcd_dvd_difference_mul_centerGcd n m 1 10 (by decide)
  exact dvd_trans hs (Nat.mul_dvd_mul_left 9 (centerGcd_dvd_9_of_branch_1_10 h))

theorem slopeGcd_dvd_9_of_branch_2_5 {n m : ℕ} (h : CurveBranch n m 2 5) :
    slopeGcd n m 2 5 ∣ 9 := by
  have hs := slopeGcd_dvd_difference_mul_centerGcd n m 2 5 (by decide)
  exact dvd_trans hs (Nat.mul_dvd_mul_left 3 (centerGcd_dvd_3_of_branch_2_5 h))

end LcmSix
