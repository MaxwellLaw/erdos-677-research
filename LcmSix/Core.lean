/-
Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
-/
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega

namespace LcmSix

/-- LCM of the positive interval `{n+1, ..., n+k}`, exactly as in Erdős 677. -/
def M (n k : ℕ) : ℕ := (Finset.Ioc n (n + k)).lcm id

/-- A recursive presentation used to prove the exact defect formula. -/
def window (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => Nat.lcm (window n k) (n + k + 1)

/-- Product of the same interval. -/
def product (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => product n k * (n + k + 1)

/-- Exact product/LCM correction, before simplifying its periodic factors. -/
def defect (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => defect n k * Nat.gcd (window n k) (n + k + 1)

lemma window_dvd_iff (n k t : ℕ) :
    window n k ∣ t ↔ ∀ i, 1 ≤ i → i ≤ k → n + i ∣ t := by
  induction k with
  | zero => simp [window]; omega
  | succ k ih =>
    simp only [window, Nat.lcm_dvd_iff, ih]
    constructor
    · rintro ⟨h, hlast⟩ i hi hik
      by_cases hi' : i ≤ k
      · exact h i hi hi'
      · have : i = k + 1 := by omega
        simpa [this, Nat.add_assoc] using hlast
    · intro h
      exact ⟨fun i hi hik => h i hi (by omega), by simpa [Nat.add_assoc] using h (k+1) (by omega) (by omega)⟩

lemma window_eq_M (n k : ℕ) : window n k = M n k := by
  apply Nat.dvd_antisymm
  · rw [window_dvd_iff]
    intro i hi hik
    exact Finset.dvd_lcm (by simp only [Finset.mem_Ioc]; omega)
  · apply Finset.lcm_dvd
    intro x hx
    have hx' : n < x ∧ x ≤ n + k := Finset.mem_Ioc.mp hx
    have hw := (window_dvd_iff n k (window n k)).mp (dvd_refl _)
    have hi : 1 ≤ x - n := by omega
    have hk : x - n ≤ k := by omega
    simpa [Nat.add_sub_of_le hx'.1.le] using hw (x-n) hi hk

lemma window_pos (n k : ℕ) : 0 < window n k := by
  induction k with
  | zero => simp [window]
  | succ k ih => exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))

lemma product_eq_defect_mul_window (n k : ℕ) :
    product n k = defect n k * window n k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [product, defect, window, ih]
    simp only [mul_assoc, Nat.gcd_mul_lcm]

lemma gcd_lcm_left (a b c : ℕ) :
    Nat.gcd (Nat.lcm a b) c = Nat.lcm (Nat.gcd a c) (Nat.gcd b c) := by
  by_cases ha : a = 0
  · simp [ha, Nat.lcm_eq_left (Nat.gcd_dvd_right b c)]
  by_cases hb : b = 0
  · simp [hb, Nat.lcm_eq_right (Nat.gcd_dvd_right a c)]
  by_cases hc : c = 0
  · simp [hc]
  have hac : Nat.gcd a c ≠ 0 := by simp [Nat.gcd_eq_zero_iff, ha]
  have hbc : Nat.gcd b c ≠ 0 := by simp [Nat.gcd_eq_zero_iff, hb]
  have hab : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha hb
  apply Nat.eq_of_factorization_eq
    (by simp [Nat.gcd_eq_zero_iff, hc]) (Nat.lcm_ne_zero hac hbc)
  intro p
  simp only [Nat.factorization_gcd hab hc, Nat.factorization_lcm ha hb,
    Nat.factorization_lcm hac hbc, Nat.factorization_gcd ha hc,
    Nat.factorization_gcd hb hc, Finsupp.inf_apply, Finsupp.sup_apply]
  exact min_max_distrib_right _ _ _

lemma gcd_shift (n i j : ℕ) (hij : i ≤ j) :
    Nat.gcd (n+i) (n+j) = Nat.gcd (n+i) (j-i) := by
  have hj : n+j = (n+i)+(j-i) := by omega
  rw [hj, Nat.gcd_self_add_right]

end LcmSix
