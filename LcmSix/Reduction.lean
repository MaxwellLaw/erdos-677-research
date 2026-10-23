/- Copyright (c) 2026 MaxwellLaw. Released under Apache 2.0. -/
import LcmSix.Core
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace LcmSix

/-- Exact periodic product/LCM factor for length six. -/
def carry (n : ℕ) : ℕ :=
  12 * (if n % 4 < 2 then 1 else 2) * (if n % 5 = 4 then 5 else 1)

lemma gcd_period_sixty (n i d : ℕ) (hd : d ∣ 60) :
    Nat.gcd (n+i) d = Nat.gcd (n % 60+i) d := by
  conv_lhs => rw [Nat.gcd_comm, Nat.gcd_rec]
  conv_rhs => rw [Nat.gcd_comm, Nat.gcd_rec]
  congr 1
  conv_lhs => rw [Nat.add_mod]
  conv_rhs => rw [Nat.add_mod, Nat.mod_mod_of_dvd n hd]

lemma defect_six (n : ℕ) : defect n 6 = carry n := by
  simp only [defect, window, gcd_lcm_left, Nat.add_zero,
    Nat.gcd_one_left, Nat.lcm_one_left, one_mul]
  rw [gcd_shift n 1 2 (by decide)]
  rw [gcd_shift n 1 3 (by decide)]
  rw [gcd_shift n 2 3 (by decide)]
  rw [gcd_shift n 1 4 (by decide)]
  rw [gcd_shift n 2 4 (by decide)]
  rw [gcd_shift n 3 4 (by decide)]
  rw [gcd_shift n 1 5 (by decide)]
  rw [gcd_shift n 2 5 (by decide)]
  rw [gcd_shift n 3 5 (by decide)]
  rw [gcd_shift n 4 5 (by decide)]
  rw [gcd_shift n 1 6 (by decide)]
  rw [gcd_shift n 2 6 (by decide)]
  rw [gcd_shift n 3 6 (by decide)]
  rw [gcd_shift n 4 6 (by decide)]
  rw [gcd_shift n 5 6 (by decide)]
  norm_num only [Nat.reduceSub]
  try rw [gcd_period_sixty n 1 1 (by decide)]
  try rw [gcd_period_sixty n 1 2 (by decide)]
  try rw [gcd_period_sixty n 1 3 (by decide)]
  try rw [gcd_period_sixty n 1 4 (by decide)]
  try rw [gcd_period_sixty n 1 5 (by decide)]
  try rw [gcd_period_sixty n 2 1 (by decide)]
  try rw [gcd_period_sixty n 2 2 (by decide)]
  try rw [gcd_period_sixty n 2 3 (by decide)]
  try rw [gcd_period_sixty n 2 4 (by decide)]
  try rw [gcd_period_sixty n 3 1 (by decide)]
  try rw [gcd_period_sixty n 3 2 (by decide)]
  try rw [gcd_period_sixty n 3 3 (by decide)]
  try rw [gcd_period_sixty n 4 1 (by decide)]
  try rw [gcd_period_sixty n 4 2 (by decide)]
  try rw [gcd_period_sixty n 5 1 (by decide)]
  have h4 : n % 4 = (n % 60) % 4 := (Nat.mod_mod_of_dvd n (by decide : 4 ∣ 60)).symm
  have h5 : n % 5 = (n % 60) % 5 := (Nat.mod_mod_of_dvd n (by decide : 5 ∣ 60)).symm
  unfold carry
  rw [h4, h5]
  have hr : n % 60 < 60 := Nat.mod_lt n (by decide)
  interval_cases hr' : n % 60 <;> norm_num

lemma carry_pos (n : ℕ) : 0 < carry n := by
  unfold carry
  split_ifs <;> norm_num

lemma carry_values (n : ℕ) : carry n = 12 ∨ carry n = 24 ∨ carry n = 60 ∨ carry n = 120 := by
  unfold carry
  split_ifs <;> norm_num

lemma product_six (n : ℕ) : product n 6 = carry n * M n 6 := by
  rw [product_eq_defect_mul_window, defect_six, window_eq_M]

lemma M_pos (n k : ℕ) : 0 < M n k := by
  rw [← window_eq_M]
  exact window_pos n k

lemma product_pos (n k : ℕ) : 0 < product n k := by
  induction k with
  | zero => simp [product]
  | succ k ih => exact Nat.mul_pos ih (by omega)

lemma product_mono {n m : ℕ} (h : n ≤ m) (k : ℕ) : product n k ≤ product m k := by
  induction k with
  | zero => rfl
  | succ k ih => exact Nat.mul_le_mul ih (by omega)

lemma product_lt {n m k : ℕ} (h : n < m) (hk : 0 < k) : product n k < product m k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  calc
    product n (j+1) = product n j * (n+j+1) := rfl
    _ ≤ product m j * (n+j+1) := Nat.mul_le_mul_right _ (product_mono h.le j)
    _ < product m j * (m+j+1) := Nat.mul_lt_mul_of_pos_left (by omega) (product_pos m j)
    _ = product m (j+1) := rfl

/-- An infinite-family exclusion furnished by the exact factor, not the full k=6 claim. -/
theorem no_collision_of_carry_le {n m : ℕ} (hnm : n < m)
    (hc : carry m ≤ carry n) : M m 6 ≠ M n 6 := by
  intro h
  have hp := product_lt hnm (by decide : 0 < 6)
  rw [product_six n, product_six m, h] at hp
  have : carry n < carry m := (Nat.mul_lt_mul_right (M_pos n 6)).mp hp
  omega

/-- Retains the exact periodic factor equation, not only a product ratio. -/
def ProductBranch (n m a b : ℕ) : Prop :=
  a * carry m = b * carry n ∧ a * product m 6 = b * product n 6

lemma branch_implies_collision {n m a b : ℕ} (ha : 0 < a)
    (h : ProductBranch n m a b) : M m 6 = M n 6 := by
  rcases h with ⟨hc, hp⟩
  rw [product_six, product_six, ← mul_assoc, ← mul_assoc, ← hc] at hp
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos ha (carry_pos m)) hp

/-- Exact four-branch reduction. This does not assert that any branch is empty. -/
theorem collision_iff_product_branches {n m : ℕ} (hnm : n < m) :
    M m 6 = M n 6 ↔
      ProductBranch n m 1 2 ∨ ProductBranch n m 1 5 ∨
      ProductBranch n m 1 10 ∨ ProductBranch n m 2 5 := by
  constructor
  · intro h
    have hp := product_lt hnm (by decide : 0 < 6)
    have pn := product_six n
    have pm := product_six m
    rw [h] at pm
    have hc : carry n < carry m := by
      rw [pn, pm] at hp
      exact (Nat.mul_lt_mul_right (M_pos n 6)).mp hp
    rcases carry_values n with hn | hn | hn | hn <;>
      rcases carry_values m with hm | hm | hm | hm <;>
      simp only [hn, hm] at hc pn pm ⊢ <;>
      norm_num at hc <;>
      norm_num [ProductBranch, hn, hm, pn, pm, ← mul_assoc]
  · rintro (h | h | h | h)
    · exact branch_implies_collision (by decide) h
    · exact branch_implies_collision (by decide) h
    · exact branch_implies_collision (by decide) h
    · exact branch_implies_collision (by decide) h

/-- Centered cubic from the length-six product. Subtraction is in the integers. -/
def Phi (t : ℤ) : ℤ := (t-1)*(t-9)*(t-25)

def center (n : ℕ) : ℤ := 2*(n:ℤ)+7

lemma centered_product (n : ℕ) : Phi (center n ^ 2) = 64*(product n 6 : ℤ) := by
  simp [Phi, center, product]
  ring

/-- The curve equation together with its exact residue/carry constraint. -/
def CurveBranch (n m a b : ℕ) : Prop :=
  a * carry m = b * carry n ∧
  (a:ℤ) * Phi (center m ^ 2) = (b:ℤ) * Phi (center n ^ 2)

lemma curveBranch_iff_productBranch (n m a b : ℕ) :
    CurveBranch n m a b ↔ ProductBranch n m a b := by
  unfold CurveBranch ProductBranch
  apply and_congr_right
  intro _
  rw [centered_product, centered_product]
  constructor
  · intro h
    have h' : (a:ℤ)*(product m 6 : ℤ) = (b:ℤ)*(product n 6 : ℤ) := by nlinarith [h]
    exact_mod_cast h'
  · intro h
    have h' : (a:ℤ)*(product m 6 : ℤ) = (b:ℤ)*(product n 6 : ℤ) := by exact_mod_cast h
    nlinarith [h']

/-- A complete equivalence in the original disjoint, equal-length positive-interval
range. Proving emptiness of the four right-hand branches remains an open obligation. -/
theorem collision_iff_four_curves {n m : ℕ} (hdisjoint : n+6 ≤ m) :
    M m 6 = M n 6 ↔
      CurveBranch n m 1 2 ∨ CurveBranch n m 1 5 ∨
      CurveBranch n m 1 10 ∨ CurveBranch n m 2 5 := by
  simp only [curveBranch_iff_productBranch]
  exact collision_iff_product_branches (by omega)

lemma center_constraints {n m : ℕ} (hdisjoint : n+6 ≤ m) :
    Odd (center n) ∧ Odd (center m) ∧ 7 ≤ center n ∧
      12 ≤ center m - center n := by
  constructor
  · exact ⟨(n:ℤ)+3, by simp [center]; ring⟩
  constructor
  · exact ⟨(m:ℤ)+3, by simp [center]; ring⟩
  simp only [center]
  omega

end LcmSix
