/-
Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
-/
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.Order.Basic

namespace LcmSix.LatticeDistance

/-- An integral dual functional on the rounded four-dimensional lattice. -/
structure Certificate where
  a1 : ℤ
  a2 : ℤ
  a3 : ℤ
  a0 : ℤ
  target : ℤ
  w1 : ℤ
  w2 : ℤ
  w3 : ℤ
  w4 : ℤ
  denominator : ℤ
  q1 : ℤ
  q2 : ℤ
  q3 : ℤ
  q4 : ℤ
  qt : ℤ
  remainder : ℤ
  delta : ℤ
  threshold : ℤ

/-- All obligations are explicit integer identities or inequalities. -/
def Certificate.Valid (c : Certificate) : Prop :=
  0 < c.denominator ∧ 0 ≤ c.delta ∧ c.delta ≤ c.remainder ∧
  c.delta ≤ c.denominator - c.remainder ∧
  c.w1 + c.w4 * c.a1 = c.denominator * c.q1 ∧
  c.w2 + c.w4 * c.a2 = c.denominator * c.q2 ∧
  c.w3 + c.w4 * c.a3 = c.denominator * c.q3 ∧
  c.w4 * c.a0 = c.denominator * c.q4 ∧
  c.w4 * c.target = c.denominator * c.qt + c.remainder ∧
  (c.w1^2 + c.w2^2 + c.w3^2 + c.w4^2) * c.threshold < c.delta^2

theorem residue_square_lower (d r δ k : ℤ) (hd : 0 < d)
    (hδ : 0 ≤ δ) (hr : δ ≤ r) (hdr : δ ≤ d-r) :
    δ^2 ≤ (d*k-r)^2 := by
  by_cases hk : k ≤ 0
  · have hdk : d*k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hd) hk
    have h : δ ≤ -(d*k-r) := by omega
    nlinarith [sq_nonneg (-(d*k-r)-δ)]
  · have hk1 : 1 ≤ k := by omega
    have hdk : d ≤ d*k := by nlinarith
    have h : δ ≤ d*k-r := by omega
    nlinarith [sq_nonneg ((d*k-r)-δ)]

theorem cauchy_four (w1 w2 w3 w4 v1 v2 v3 v4 : ℤ) :
    (w1*v1+w2*v2+w3*v3+w4*v4)^2 ≤
      (w1^2+w2^2+w3^2+w4^2)*(v1^2+v2^2+v3^2+v4^2) := by
  nlinarith [sq_nonneg (w1*v2-w2*v1), sq_nonneg (w1*v3-w3*v1),
    sq_nonneg (w1*v4-w4*v1), sq_nonneg (w2*v3-w3*v2),
    sq_nonneg (w2*v4-w4*v2), sq_nonneg (w3*v4-w4*v3)]

/-- Every integer lattice vector is strictly outside the certified squared radius. -/
theorem Certificate.excludes_ball (c : Certificate) (hc : c.Valid)
    (m1 m2 m3 m0 : ℤ) :
    c.threshold < m1^2+m2^2+m3^2+
      (c.a1*m1+c.a2*m2+c.a3*m3+c.a0*m0-c.target)^2 := by
  rcases hc with ⟨hd,hδ,hr,hdr,h1,h2,h3,h4,ht,hs⟩
  let v4 := c.a1*m1+c.a2*m2+c.a3*m3+c.a0*m0-c.target
  have heq : c.w1*m1+c.w2*m2+c.w3*m3+c.w4*v4 =
      c.denominator*(c.q1*m1+c.q2*m2+c.q3*m3+c.q4*m0-c.qt)-c.remainder := by
    dsimp [v4]
    linear_combination m1*h1 + m2*h2 + m3*h3 + m0*h4 - ht
  have hl := residue_square_lower c.denominator c.remainder c.delta
    (c.q1*m1+c.q2*m2+c.q3*m3+c.q4*m0-c.qt) hd hδ hr hdr
  rw [← heq] at hl
  have hu := cauchy_four c.w1 c.w2 c.w3 c.w4 m1 m2 m3 v4
  have hn : 0 ≤ c.w1^2+c.w2^2+c.w3^2+c.w4^2 := by positivity
  have hout : c.threshold < m1^2+m2^2+m3^2+v4^2 := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_left (le_of_not_gt h) hn
    nlinarith
  exact hout

/-- Bounding the first three coordinates forces a large last coordinate. -/
theorem Certificate.last_coordinate_large (c : Certificate) (hc : c.Valid)
    (B H m1 m2 m3 m0 : ℤ) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hT : c.threshold = 3*B^2+H^2)
    (h1 : |m1| ≤ B) (h2 : |m2| ≤ B) (h3 : |m3| ≤ B) :
    H < |c.a1*m1+c.a2*m2+c.a3*m3+c.a0*m0-c.target| := by
  have hs1 : m1^2 ≤ B^2 := (sq_le_sq).2 (by simpa [abs_of_nonneg hB] using h1)
  have hs2 : m2^2 ≤ B^2 := (sq_le_sq).2 (by simpa [abs_of_nonneg hB] using h2)
  have hs3 : m3^2 ≤ B^2 := (sq_le_sq).2 (by simpa [abs_of_nonneg hB] using h3)
  have hd := c.excludes_ball hc m1 m2 m3 m0
  rw [hT] at hd
  by_contra h
  have hv : (c.a1*m1+c.a2*m2+c.a3*m3+c.a0*m0-c.target)^2 ≤ H^2 :=
    (sq_le_sq).2 (by simpa [abs_of_nonneg hH] using le_of_not_gt h)
  linarith

end LcmSix.LatticeDistance
