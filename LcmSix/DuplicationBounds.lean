/-
Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
-/
import LcmSix.HeightCertificates
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
Real quartic inequalities used in the global canonical-height lower bound.
These definitions agree with the integer duplication polynomials, but the
results here are purely polynomial inequalities, not height or elliptic-curve
assertions. Concrete Bernstein certificates are in DuplicationCertificates.
-/

namespace LcmSix.DuplicationBounds

/-- The homogeneous numerator of the x-coordinate duplication formula. -/
def F (a b c p q : ℝ) : ℝ :=
  p^4 - 2*b*p^2*q^2 - 8*c*p*q^3 + (b^2-4*a*c)*q^4

/-- The corresponding homogeneous denominator. -/
def G (a b c p q : ℝ) : ℝ :=
  4*(p^3*q + a*p^2*q^2 + b*p*q^3 + c*q^4)

def pairNorm (a b c p q : ℝ) : ℝ := max |F a b c p q| |G a b c p q|

/-- An expanded degree-four Bernstein expression. -/
def bernstein4 (c0 c1 c2 c3 c4 t : ℝ) : ℝ :=
  c0*(1-t)^4 + 4*c1*t*(1-t)^3 + 6*c2*t^2*(1-t)^2 +
    4*c3*t^3*(1-t) + c4*t^4

theorem bernstein4_nonneg {c0 c1 c2 c3 c4 t : ℝ}
    (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2)
    (h3 : 0 ≤ c3) (h4 : 0 ≤ c4) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ bernstein4 c0 c1 c2 c3 c4 t := by
  have hs : 0 ≤ 1-t := sub_nonneg.mpr ht1
  unfold bernstein4
  positivity

/-- Transfer one exact Bernstein identity to every point of a real interval. -/
theorem lower_bound_of_bernstein {f : ℝ → ℝ} {L U c0 c1 c2 c3 c4 : ℝ}
    (hLU : L < U)
    (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2)
    (h3 : 0 ≤ c3) (h4 : 0 ≤ c4)
    (hid : ∀ t : ℝ, 32*f (L+(U-L)*t)-1 = bernstein4 c0 c1 c2 c3 c4 t)
    {x : ℝ} (hxL : L ≤ x) (hxU : x ≤ U) : 1 ≤ 32*f x := by
  let t := (x-L)/(U-L)
  have hpos : 0 < U-L := sub_pos.mpr hLU
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hxL) (le_of_lt hpos)
  have ht1 : t ≤ 1 := (div_le_one hpos).mpr (by linarith)
  have hx : L+(U-L)*t = x := by
    dsimp [t]
    field_simp
    ring
  have hn := bernstein4_nonneg h0 h1 h2 h3 h4 ht0 ht1
  rw [← hid, hx] at hn
  linarith

theorem F_cast (a b c p q : ℤ) :
    F a b c p q = (HeightCertificates.F a b c p q : ℝ) := by
  simp only [F, HeightCertificates.F, HeightCertificates.homogeneousQuartic]
  push_cast
  ring

theorem G_cast (a b c p q : ℤ) :
    G a b c p q = (HeightCertificates.G a b c p q : ℝ) := by
  simp only [G, HeightCertificates.G, HeightCertificates.homogeneousQuartic]
  push_cast
  ring

theorem F_homogeneous (a b c p q t : ℝ) :
    F a b c (p*t) (q*t) = t^4 * F a b c p q := by
  unfold F
  ring

theorem G_homogeneous (a b c p q t : ℝ) :
    G a b c (p*t) (q*t) = t^4 * G a b c p q := by
  unfold G
  ring

theorem pairNorm_homogeneous (a b c p q t : ℝ) :
    pairNorm a b c (p*t) (q*t) = t^4 * pairNorm a b c p q := by
  unfold pairNorm
  rw [F_homogeneous, G_homogeneous, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ t^4)]
  exact (mul_max_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ t^4)).symm

/-- Two compact charts cover the entire real projective line, including q=0. -/
theorem global_bound_of_charts {a b c : ℝ}
    (hfinite : ∀ t : ℝ, |t| ≤ 1 → 1 ≤ 32*pairNorm a b c t 1)
    (hrecip : ∀ t : ℝ, |t| ≤ 1 → 1 ≤ 32*pairNorm a b c 1 t)
    (p q : ℝ) : max |p| |q| ^ 4 ≤ 32*pairNorm a b c p q := by
  rcases le_total |p| |q| with hpq | hqp
  · by_cases hq : q = 0
    · have hp : p = 0 := abs_eq_zero.mp (le_antisymm (by simpa [hq] using hpq) (abs_nonneg p))
      subst p
      subst q
      norm_num [pairNorm, F, G]
    have habsq : 0 < |q| := abs_pos.mpr hq
    have ht : |p/q| ≤ 1 := by rw [abs_div]; exact (div_le_one habsq).mpr hpq
    have h := mul_le_mul_of_nonneg_left (hfinite (p/q) ht) (by positivity : (0 : ℝ) ≤ q^4)
    have he := pairNorm_homogeneous a b c (p/q) 1 q
    simp only [div_mul_cancel₀ p hq, one_mul] at he
    rw [max_eq_right hpq, (show Even (4 : ℕ) by decide).pow_abs]
    calc
      q^4 = q^4*1 := by ring
      _ ≤ q^4*(32*pairNorm a b c (p/q) 1) := h
      _ = 32*pairNorm a b c p q := by rw [he]; ring
  · by_cases hp : p = 0
    · have hq : q = 0 := abs_eq_zero.mp (le_antisymm (by simpa [hp] using hqp) (abs_nonneg q))
      subst p
      subst q
      norm_num [pairNorm, F, G]
    have habsp : 0 < |p| := abs_pos.mpr hp
    have ht : |q/p| ≤ 1 := by rw [abs_div]; exact (div_le_one habsp).mpr hqp
    have h := mul_le_mul_of_nonneg_left (hrecip (q/p) ht) (by positivity : (0 : ℝ) ≤ p^4)
    have he := pairNorm_homogeneous a b c 1 (q/p) p
    simp only [div_mul_cancel₀ q hp, one_mul] at he
    rw [max_eq_left hqp, (show Even (4 : ℕ) by decide).pow_abs]
    calc
      p^4 = p^4*1 := by ring
      _ ≤ p^4*(32*pairNorm a b c 1 (q/p)) := h
      _ = 32*pairNorm a b c p q := by rw [he]; ring

end LcmSix.DuplicationBounds
