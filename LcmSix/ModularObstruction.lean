import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# A limitation of congruence-only sieves for the length-six reduction

These theorems are **not LCM collision examples**. They say that, for every
positive modulus, positive disjoint pairs survive the reduced product equation
modulo that modulus, even with the exact carry residue constraints. No equality
of integer products or LCMs is claimed.

Author: MaxwellLaw.
-/

namespace LcmSix.ModularObstruction

/-- The product polynomial on integers, allowing its six trivial roots. -/
def productSix (n : ℤ) : ℤ :=
  (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) * (n + 6)

lemma productSix_congr {q n m : ℤ} (h : n ≡ m [ZMOD q]) :
    productSix n ≡ productSix m [ZMOD q] := by
  exact (((((h.add_right 1).mul (h.add_right 2)).mul (h.add_right 3)).mul
    (h.add_right 4)).mul (h.add_right 5)).mul (h.add_right 6)

private lemma shifted_root {q c r : ℤ} (hr : productSix r = 0) :
    productSix (c * q + r) ≡ 0 [ZMOD q] := by
  have h : c * q + r ≡ r [ZMOD q] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-c, ?_⟩
    ring
  simpa [hr] using productSix_congr h

/-- Every positive modulus admits positive disjoint representatives passing the
ratio-2 product congruence and its carry filters. This is not a collision. -/
theorem ratio_two_survives_every_modulus (q : ℤ) (hq : 1 ≤ q) :
    ∃ n m : ℤ, 0 ≤ n ∧ n + 6 ≤ m ∧
      n % 4 = 1 ∧ m % 4 = 2 ∧ n % 5 = 2 ∧ m % 5 = 3 ∧
      productSix m ≡ 2 * productSix n [ZMOD q] := by
  refine ⟨20 * q - 3, 40 * q - 2, by omega, by omega,
    by omega, by omega, by omega, by omega, ?_⟩
  have hn : productSix (20 * q - 3) ≡ 0 [ZMOD q] :=
    shifted_root (q := q) (c := 20) (r := -3) (by norm_num [productSix])
  have hm : productSix (40 * q - 2) ≡ 0 [ZMOD q] :=
    shifted_root (q := q) (c := 40) (r := -2) (by norm_num [productSix])
  exact hm.trans (by simpa using (hn.mul_left 2).symm)

/-- Every positive modulus admits positive disjoint representatives passing the
ratio-5 product congruence and its carry filters. This is not a collision. -/
theorem ratio_five_survives_every_modulus (q : ℤ) (hq : 1 ≤ q) :
    ∃ n m : ℤ, 0 ≤ n ∧ n + 6 ≤ m ∧
      n % 4 = 2 ∧ m % 4 = 3 ∧ n % 5 = 3 ∧ m % 5 = 4 ∧
      productSix m ≡ 5 * productSix n [ZMOD q] := by
  refine ⟨20 * q - 2, 40 * q - 1, by omega, by omega,
    by omega, by omega, by omega, by omega, ?_⟩
  have hn : productSix (20 * q - 2) ≡ 0 [ZMOD q] :=
    shifted_root (q := q) (c := 20) (r := -2) (by norm_num [productSix])
  have hm : productSix (40 * q - 1) ≡ 0 [ZMOD q] :=
    shifted_root (q := q) (c := 40) (r := -1) (by norm_num [productSix])
  exact hm.trans (by simpa using (hn.mul_left 5).symm)

/-- Every positive modulus admits positive disjoint representatives passing the
ratio-10 product congruence and its carry filters. This is not a collision. -/
theorem ratio_ten_survives_every_modulus (q : ℤ) (hq : 1 ≤ q) :
    ∃ n m : ℤ, 0 ≤ n ∧ n + 6 ≤ m ∧
      n % 4 = 1 ∧ m % 4 = 3 ∧ n % 5 = 2 ∧ m % 5 = 4 ∧
      productSix m ≡ 10 * productSix n [ZMOD q] := by
  refine ⟨20 * q - 3, 40 * q - 1, by omega, by omega,
    by omega, by omega, by omega, by omega, ?_⟩
  have hn : productSix (20 * q - 3) ≡ 0 [ZMOD q] :=
    shifted_root (q := q) (c := 20) (r := -3) (by norm_num [productSix])
  have hm : productSix (40 * q - 1) ≡ 0 [ZMOD q] :=
    shifted_root (q := q) (c := 40) (r := -1) (by norm_num [productSix])
  exact hm.trans (by simpa using (hn.mul_left 10).symm)

private lemma carry_sixty_root (A B : ℕ) (hA : 4 ∣ A) (hB : 5 ∣ B)
    (hApos : 0 < A) (hBpos : 0 < B) (hcop : A.Coprime B) :
    ∃ c : ℕ, c % 4 = 1 ∧ c % 5 = 4 ∧
      (A : ℤ) * (B : ℤ) ∣ productSix (c : ℤ) := by
  let c := Nat.chineseRemainder hcop (A - 3) (B - 1)
  have hA3 : 3 ≤ A := by
    have := Nat.le_of_dvd hApos hA
    omega
  have hB1 : 1 ≤ B := by omega
  have hc4 : (c : ℕ) % 4 = 1 := by
    have hh := c.property.1.of_dvd hA
    have h0 := Nat.mod_eq_zero_of_dvd hA
    unfold Nat.ModEq at hh
    omega
  have hc5 : (c : ℕ) % 5 = 4 := by
    have hh := c.property.2.of_dvd hB
    have h0 := Nat.mod_eq_zero_of_dvd hB
    unfold Nat.ModEq at hh
    omega
  have hcA : (A : ℤ) ∣ (c : ℕ) + 3 := by
    have hh := c.property.1.dvd
    have he : ((A - 3 : ℕ) : ℤ) = (A : ℤ) - 3 := by omega
    rw [he] at hh
    have h0 := dvd_sub (dvd_refl (A : ℤ)) hh
    have hid : (A : ℤ) - ((A : ℤ) - 3 - (c : ℕ)) = (c : ℕ) + 3 := by ring
    rw [hid] at h0
    exact h0
  have hcB : (B : ℤ) ∣ (c : ℕ) + 1 := by
    have hh := c.property.2.dvd
    have he : ((B - 1 : ℕ) : ℤ) = (B : ℤ) - 1 := by omega
    rw [he] at hh
    have h0 := dvd_sub (dvd_refl (B : ℤ)) hh
    have hid : (B : ℤ) - ((B : ℤ) - 1 - (c : ℕ)) = (c : ℕ) + 1 := by ring
    rw [hid] at h0
    exact h0
  refine ⟨c, hc4, hc5, ?_⟩
  have hp := mul_dvd_mul hcA hcB
  have hid : productSix (c : ℕ) =
      (((c : ℕ) + 3 : ℤ) * ((c : ℕ) + 1)) *
      (((c : ℕ) + 2 : ℤ) * ((c : ℕ) + 4) * ((c : ℕ) + 5) * ((c : ℕ) + 6)) := by
    unfold productSix
    ring
  rw [hid]
  exact dvd_mul_of_dvd_left hp _

set_option maxHeartbeats 200000 in
/-- The remaining ratio 5/2 also survives every positive modulus, with its exact
carry residues. CRT places the 2-primary and odd parts at different roots. -/
theorem ratio_five_halves_survives_every_modulus (q : ℕ) (hq : 0 < q) :
    ∃ n m : ℤ, 0 ≤ n ∧ n + 6 ≤ m ∧
      n % 4 = 2 ∧ m % 4 = 1 ∧ n % 5 = 3 ∧ m % 5 = 4 ∧
      2 * productSix m ≡ 5 * productSix n [ZMOD (q : ℤ)] := by
  obtain ⟨k, r, hr, hqfac⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.ne_of_gt hq)
  let A : ℕ := 2 ^ (k + 2)
  let B := 5 * r
  have hA : 4 ∣ A := by
    refine ⟨2 ^ k, ?_⟩
    dsimp [A]
    rw [pow_add]
    ring
  have hB : 5 ∣ B := ⟨r, rfl⟩
  have hApos : 0 < A := pow_pos (by decide) _
  have hrpos : 0 < r := hr.pos
  have hBpos : 0 < B := Nat.mul_pos (by decide) hrpos
  have hcop : A.Coprime B := by
    apply Nat.Coprime.pow_left
    exact Nat.coprime_two_left.mpr ((by decide : Odd (5 : ℕ)).mul hr)
  obtain ⟨c, hc4, hc5, hcP⟩ := carry_sixty_root A B hA hB hApos hBpos hcop
  have hAB : A * B = 20 * q := by
    dsimp [A, B]
    rw [hqfac, pow_add]
    ring
  have hqP : (q : ℤ) ∣ productSix (c : ℤ) := by
    have hh : (q : ℤ) ∣ (A : ℤ) * (B : ℤ) := by
      have he : (A : ℤ) * (B : ℤ) = 20 * (q : ℤ) := by exact_mod_cast hAB
      rw [he]
      exact dvd_mul_left _ _
    exact hh.trans hcP
  have hc4z : (c : ℤ) % 4 = 1 := by exact_mod_cast hc4
  have hc5z : (c : ℤ) % 5 = 4 := by exact_mod_cast hc5
  clear k r hr hqfac A B hA hB hApos hrpos hBpos hcop hAB hc4 hc5 hcP
  have hqz : (1 : ℤ) ≤ q := by omega
  refine ⟨20 * (q : ℤ) - 2, (c : ℤ) + 40 * q, by omega, by omega,
    by omega, by omega, by omega, by omega, ?_⟩
  have hn : productSix (20 * (q : ℤ) - 2) ≡ 0 [ZMOD (q : ℤ)] := by
    simpa only [sub_eq_add_neg] using
      (shifted_root (q := (q : ℤ)) (c := 20) (r := -2) (by norm_num [productSix]))
  have hmc : (c : ℤ) + 40 * q ≡ (c : ℤ) [ZMOD (q : ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-40, ?_⟩
    ring
  have hm : productSix ((c : ℤ) + 40 * q) ≡ 0 [ZMOD (q : ℤ)] :=
    (productSix_congr hmc).trans hqP.modEq_zero_int
  have hm2 : 2 * productSix ((c : ℤ) + 40 * q) ≡ 0 [ZMOD (q : ℤ)] := by
    simpa using hm.mul_left 2
  have hn5 : 5 * productSix (20 * (q : ℤ) - 2) ≡ 0 [ZMOD (q : ℤ)] := by
    simpa using hn.mul_left 5
  exact hm2.trans hn5.symm


end LcmSix.ModularObstruction
