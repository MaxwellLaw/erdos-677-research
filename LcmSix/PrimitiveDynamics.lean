/-
Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
-/
import LcmSix.CanonicalLimit
import LcmSix.DuplicationHeight
import LcmSix.HeightConstants
import Mathlib.RingTheory.Int.Basic

/-!
# Canonical limits for the four actual primitive quartic maps

This constructs the gcd-normalized integer-coordinate dynamics explicitly.
No claim about a rational elliptic point or its group law is an assumption.
Identifying this map with elliptic-curve duplication remains a separate step.
-/

namespace LcmSix.PrimitiveDynamics
open Filter
open scoped Topology

structure Point where
  p : ℤ
  q : ℤ
  coprime : IsCoprime p q

noncomputable def size (P : Point) : ℝ := max |(P.p : ℝ)| |(P.q : ℝ)|
noncomputable def height (P : Point) : ℝ := Real.log (size P)

lemma size_pos (P : Point) : 0 < size P := by
  have hn : P.p ≠ 0 ∨ P.q ≠ 0 := by
    by_contra h
    push Not at h
    have hc := P.coprime
    obtain ⟨u,v,hc⟩ := hc
    simp [h.1,h.2] at hc
  rcases hn with hp | hq
  · exact (abs_pos.mpr (by exact_mod_cast hp)).trans_le (le_max_left _ _)
  · exact (abs_pos.mpr (by exact_mod_cast hq)).trans_le (le_max_right _ _)

/-- Every field is discharged for the four concrete models below. -/
structure Model where
  a : ℤ
  b : ℤ
  c : ℤ
  R : ℤ
  C : ℝ
  R_pos : 0 < R
  C_pos : 0 < C
  common : ∀ (p q d : ℤ), IsCoprime p q →
    d ∣ HeightCertificates.F a b c p q → d ∣ HeightCertificates.G a b c p q → d ∣ R
  lower : ∀ (p q : ℝ), max |p| |q|^4 ≤ 32*DuplicationBounds.pairNorm a b c p q
  upper : DuplicationBounds.coefficientBound a b c ≤ C

namespace Model

def num (M : Model) (P : Point) : ℤ := HeightCertificates.F M.a M.b M.c P.p P.q
def den (M : Model) (P : Point) : ℤ := HeightCertificates.G M.a M.b M.c P.p P.q
def divisor (M : Model) (P : Point) : ℕ := Int.gcd (M.num P) (M.den P)

lemma divisor_dvd (M : Model) (P : Point) : (M.divisor P : ℤ) ∣ M.R :=
  M.common P.p P.q (M.divisor P) P.coprime
    (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)

lemma divisor_pos (M : Model) (P : Point) : 0 < M.divisor P := by
  by_contra h
  have hz : M.divisor P = 0 := by omega
  have hd := M.divisor_dvd P
  rw [hz, Nat.cast_zero, zero_dvd_iff] at hd
  linarith [M.R_pos]

/-- Divide by the actual positive gcd; this is a total map of primitive pairs. -/
def step (M : Model) (P : Point) : Point where
  p := M.num P / M.divisor P
  q := M.den P / M.divisor P
  coprime := Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd (M.divisor_pos P))

lemma size_step (M : Model) (P : Point) :
    size (M.step P) = DuplicationBounds.pairNorm M.a M.b M.c P.p P.q / (M.divisor P : ℝ) := by
  have hd : (0:ℝ) < M.divisor P := by exact_mod_cast M.divisor_pos P
  have hp : (M.num P : ℝ) = (M.step P).p * (M.divisor P : ℝ) := by
    exact_mod_cast (Int.ediv_mul_cancel (Int.gcd_dvd_left (M.num P) (M.den P))).symm
  have hq : (M.den P : ℝ) = (M.step P).q * (M.divisor P : ℝ) := by
    exact_mod_cast (Int.ediv_mul_cancel (Int.gcd_dvd_right (M.num P) (M.den P))).symm
  rw [DuplicationBounds.pairNorm, DuplicationBounds.F_cast, DuplicationBounds.G_cast]
  change size (M.step P) = max |(M.num P : ℝ)| |(M.den P : ℝ)| / (M.divisor P : ℝ)
  rw [hp, hq, abs_mul, abs_mul, abs_of_pos hd,
    ← max_mul_of_nonneg _ _ hd.le, mul_div_cancel_right₀ _ hd.ne']
  rfl

/-- An actual one-step height defect for every primitive integer input. The
coarse R-bound is sufficient for convergence; no local-square premise is used. -/
theorem height_defect (M : Model) (P : Point) :
    -Real.log (32*(M.R : ℝ)) ≤ height (M.step P)-4*height P ∧
      height (M.step P)-4*height P ≤ Real.log M.C := by
  have hd : (1:ℝ) ≤ M.divisor P := by exact_mod_cast M.divisor_pos P
  have hdR : (M.divisor P : ℝ) ≤ M.R := by
    exact_mod_cast Int.le_of_dvd M.R_pos (M.divisor_dvd P)
  dsimp only [height]
  rw [size_step]
  simpa only [size] using
    DuplicationBounds.logarithmic_defect (size_pos P) hd hdR M.C_pos M.upper (M.lower P.p P.q)

noncomputable def errorBound (M : Model) : ℝ :=
  max |Real.log (32*(M.R:ℝ))| |Real.log M.C|

lemma abs_height_defect (M : Model) (P : Point) :
    |height (M.step P)-4*height P| ≤ M.errorBound := by
  obtain ⟨hl, hu⟩ := M.height_defect P
  rw [abs_le]
  dsimp [errorBound]
  constructor
  · have := le_abs_self (Real.log (32*(M.R:ℝ)))
    have := le_max_left |Real.log (32*(M.R:ℝ))| |Real.log M.C|
    linarith
  · exact hu.trans ((le_abs_self _).trans (le_max_right _ _))

noncomputable def canonical (M : Model) : Point → ℝ := CanonicalLimit.canonical M.step height

/-- The limit exists for the actual gcd-normalized map, at every primitive input. -/
theorem tendsto_height (M : Model) (P : Point) :
    Tendsto (fun n : ℕ => (1/4:ℝ)^n * height (M.step^[n] P))
      atTop (𝓝 (M.canonical P)) :=
  CanonicalLimit.tendsto_normalized (fun n => height (M.step^[n] P)) M.errorBound
    (fun n => by simpa only [Function.iterate_succ_apply'] using M.abs_height_defect (M.step^[n] P))

theorem canonical_step (M : Model) (P : Point) :
    M.canonical (M.step P) = 4*M.canonical P :=
  CanonicalLimit.canonical_map M.step height M.errorBound M.abs_height_defect P

/-- A complete enclosure with explicit constants for every finite iteration. -/
theorem canonical_enclosure (M : Model) (P : Point) (N : ℕ) :
    (1/4:ℝ)^N * height (M.step^[N] P) - (1/4:ℝ)^N*Real.log (32*(M.R:ℝ))/3 ≤ M.canonical P ∧
    M.canonical P ≤ (1/4:ℝ)^N * height (M.step^[N] P) + (1/4:ℝ)^N*Real.log M.C/3 := by
  have he := CanonicalLimit.limit_tail_bounds (fun n => height (M.step^[n] P))
    (-Real.log (32*(M.R:ℝ))) (Real.log M.C)
    (fun n => by simpa only [Function.iterate_succ_apply'] using (M.height_defect (M.step^[n] P)).1)
    (fun n => by simpa only [Function.iterate_succ_apply'] using (M.height_defect (M.step^[n] P)).2) N
  simpa only [CanonicalLimit.normalized, canonical, CanonicalLimit.canonical,
    mul_neg, neg_div, sub_eq_add_neg] using he

/-- Characterization, now for the actual primitive-coordinate self-map. -/
theorem canonical_unique (M : Model) (H : Point → ℝ) (C : ℝ)
    (hmap : ∀ P, H (M.step P)=4*H P) (hb : ∀ P, |height P-H P| ≤ C) (P : Point) :
    M.canonical P = H P :=
  CanonicalLimit.canonical_unique M.step height H C hmap hb P

/-- The same strict upper error used in the length-six analytic proof, now for
this actual coordinate dynamics rather than an assumed height sequence. -/
theorem height_error_lt_five (M : Model) (hC : M.C ≤ 3061008) (P : Point) :
    M.canonical P - height P < 5 := by
  have hu := (M.canonical_enclosure P 0).2
  simp only [pow_zero, Function.iterate_zero_apply, one_mul] at hu
  have hc := HeightConstants.log_C_div_three_lt_five M.C_pos hC
  linarith

end Model


/-- Concrete model with every required polynomial and divisibility premise proved. -/
noncomputable def branch1_2 : Model where
  a := -1
  b := -65
  c := 261
  R := 47362584674304
  C := 7488
  R_pos := by norm_num
  C_pos := by norm_num
  common := fun _ _ _ hc hf hg => HeightCertificates.Branch1_2.common_divisor_bound hc hf hg
  lower := by simpa only [DuplicationBounds.pairNorm, Int.cast_neg, Int.cast_ofNat, Int.cast_one] using DuplicationBounds.Branch1_2.global_lower
  upper := by
    norm_num only [Int.cast_neg, Int.cast_ofNat, Int.cast_one]
    exact le_of_eq DuplicationBounds.Branch1_2.coefficient_bound

theorem branch1_2_converges (P : Point) :
    Tendsto (fun n : ℕ => (1/4:ℝ)^n * height (branch1_2.step^[n] P))
      atTop (𝓝 (branch1_2.canonical P)) := branch1_2.tendsto_height P

/-- Concrete model with every required polynomial and divisibility premise proved. -/
noncomputable def branch1_5 : Model where
  a := -1
  b := -408
  c := 6912
  R := 239541243494400000000
  C := 250225
  R_pos := by norm_num
  C_pos := by norm_num
  common := fun _ _ _ hc hf hg => HeightCertificates.Branch1_5.common_divisor_bound hc hf hg
  lower := by simpa only [DuplicationBounds.pairNorm, Int.cast_neg, Int.cast_ofNat, Int.cast_one] using DuplicationBounds.Branch1_5.global_lower
  upper := by
    norm_num only [Int.cast_neg, Int.cast_ofNat, Int.cast_one]
    exact le_of_eq DuplicationBounds.Branch1_5.coefficient_bound

theorem branch1_5_converges (P : Point) :
    Tendsto (fun n : ℕ => (1/4:ℝ)^n * height (branch1_5.step^[n] P))
      atTop (𝓝 (branch1_5.canonical P)) := branch1_5.tendsto_height P

/-- Concrete model with every required polynomial and divisibility premise proved. -/
noncomputable def branch1_10 : Model where
  a := 1
  b := -1633
  c := 97763
  R := 15179797184495846400000000
  C := 3061008
  R_pos := by norm_num
  C_pos := by norm_num
  common := fun _ _ _ hc hf hg => HeightCertificates.Branch1_10.common_divisor_bound hc hf hg
  lower := by simpa only [DuplicationBounds.pairNorm, Int.cast_neg, Int.cast_ofNat, Int.cast_one] using DuplicationBounds.Branch1_10.global_lower
  upper := by
    norm_num only [Int.cast_neg, Int.cast_ofNat, Int.cast_one]
    exact le_of_eq DuplicationBounds.Branch1_10.coefficient_bound

theorem branch1_10_converges (P : Point) :
    Tendsto (fun n : ℕ => (1/4:ℝ)^n * height (branch1_10.step^[n] P))
      atTop (𝓝 (branch1_10.canonical P)) := branch1_10.tendsto_height P

/-- Concrete model with every required polynomial and divisibility premise proved. -/
noncomputable def branch2_5 : Model where
  a := 1
  b := -1633
  c := 32963
  R := 42499768578278400000000
  C := 2801808
  R_pos := by norm_num
  C_pos := by norm_num
  common := fun _ _ _ hc hf hg => HeightCertificates.Branch2_5.common_divisor_bound hc hf hg
  lower := by simpa only [DuplicationBounds.pairNorm, Int.cast_neg, Int.cast_ofNat, Int.cast_one] using DuplicationBounds.Branch2_5.global_lower
  upper := by
    norm_num only [Int.cast_neg, Int.cast_ofNat, Int.cast_one]
    exact le_of_eq DuplicationBounds.Branch2_5.coefficient_bound

theorem branch2_5_converges (P : Point) :
    Tendsto (fun n : ℕ => (1/4:ℝ)^n * height (branch2_5.step^[n] P))
      atTop (𝓝 (branch2_5.canonical P)) := branch2_5.tendsto_height P


theorem branch1_2_height_error (P : Point) :
    branch1_2.canonical P - height P < 5 :=
  branch1_2.height_error_lt_five (by norm_num [branch1_2]) P

theorem branch1_5_height_error (P : Point) :
    branch1_5.canonical P - height P < 5 :=
  branch1_5.height_error_lt_five (by norm_num [branch1_5]) P

theorem branch1_10_height_error (P : Point) :
    branch1_10.canonical P - height P < 5 :=
  branch1_10.height_error_lt_five (by norm_num [branch1_10]) P

theorem branch2_5_height_error (P : Point) :
    branch2_5.canonical P - height P < 5 :=
  branch2_5.height_error_lt_five (by norm_num [branch2_5]) P

end LcmSix.PrimitiveDynamics
