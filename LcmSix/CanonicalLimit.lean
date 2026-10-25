/-
Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The normalized duplication-height limit

This module proves the analytic limit and its geometric error estimates from
an explicit bounded duplication defect. It does not assume or prove that any
particular elliptic curve's naive height satisfies those hypotheses. It also
does not assert the parallelogram law or the complete length-six endpoint.
-/

namespace LcmSix.CanonicalLimit
open Filter
open scoped Topology

/-- The normalized sequence, with the x-coordinate height convention. -/
noncomputable def normalized (s : ℕ → ℝ) (n : ℕ) : ℝ := (1 / 4 : ℝ)^n * s n

lemma normalized_step (s : ℕ → ℝ) (n : ℕ) :
    normalized s (n+1) - normalized s n =
      (1/4 : ℝ)^(n+1) * (s (n+1) - 4*s n) := by
  simp only [normalized, pow_succ]
  ring

/-- Bounded duplication defects give convergence, without a height-theory axiom. -/
theorem normalized_cauchy (s : ℕ → ℝ) (C : ℝ)
    (hb : ∀ n, |s (n+1) - 4*s n| ≤ C) :
    CauchySeq (normalized s) := by
  apply cauchySeq_of_le_geometric (1/4 : ℝ) (C/4) (by norm_num)
  intro n
  rw [Real.dist_eq, abs_sub_comm, normalized_step, abs_mul, abs_of_nonneg (by positivity)]
  have h := mul_le_mul_of_nonneg_left (hb n) (by positivity : 0 ≤ (1/4 : ℝ)^(n+1))
  rw [pow_succ] at h
  calc
    _ ≤ (1/4 : ℝ)^n * (1/4) * C := h
    _ = C/4 * (1/4 : ℝ)^n := by ring

/-- Limit of the normalized sequence. Existence is proved under the explicit defect bound. -/
noncomputable def limit (s : ℕ → ℝ) : ℝ := limUnder atTop (normalized s)

theorem tendsto_normalized (s : ℕ → ℝ) (C : ℝ)
    (hb : ∀ n, |s (n+1) - 4*s n| ≤ C) :
    Tendsto (normalized s) atTop (𝓝 (limit s)) :=
  tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (normalized_cauchy s C hb))

lemma normalized_lower (s : ℕ → ℝ) (A : ℝ)
    (hb : ∀ n, A ≤ s (n+1) - 4*s n) (n : ℕ) :
    s 0 + A/3 * (1-(1/4 : ℝ)^n) ≤ normalized s n := by
  induction n with
  | zero => simp [normalized]
  | succ n ih =>
    have hp : 0 ≤ (1/4 : ℝ)^(n+1) := by positivity
    have h := mul_le_mul_of_nonneg_left (hb n) hp
    rw [← normalized_step] at h
    rw [pow_succ] at h ⊢
    nlinarith

lemma normalized_upper (s : ℕ → ℝ) (B : ℝ)
    (hb : ∀ n, s (n+1) - 4*s n ≤ B) (n : ℕ) :
    normalized s n ≤ s 0 + B/3 * (1-(1/4 : ℝ)^n) := by
  have h := normalized_lower (fun n => -s n) (-B) (fun n => by linarith [hb n]) n
  simp only [normalized, mul_neg] at h ⊢
  linarith

/-- The asymmetric error has the same direction as the duplication defect. -/
theorem limit_bounds (s : ℕ → ℝ) (A B : ℝ)
    (hA : ∀ n, A ≤ s (n+1) - 4*s n)
    (hB : ∀ n, s (n+1) - 4*s n ≤ B) :
    s 0 + A/3 ≤ limit s ∧ limit s ≤ s 0 + B/3 := by
  have hab : ∀ n, |s (n+1)-4*s n| ≤ max |A| |B| := by
    intro n
    rw [abs_le]
    constructor
    · have := neg_abs_le A; have := le_max_left |A| |B|; linarith [hA n]
    · exact (hB n).trans ((le_abs_self B).trans (le_max_right _ _))
  have hs := tendsto_normalized s (max |A| |B|) hab
  have hr : Tendsto (fun n : ℕ => (1/4 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim (c : ℝ) : Tendsto (fun n => s 0 + c/3 * (1-(1/4 : ℝ)^n)) atTop
      (𝓝 (s 0+c/3)) := by
    simpa using ((hr.const_sub 1).const_mul (c/3)).const_add (s 0)
  exact ⟨le_of_tendsto_of_tendsto (hlim A) hs (Filter.Eventually.of_forall (normalized_lower s A hA)),
    le_of_tendsto_of_tendsto hs (hlim B) (Filter.Eventually.of_forall (normalized_upper s B hB))⟩

/-- Shifting the starting point scales the limit by the same factor as the recurrence. -/
theorem limit_shift (s : ℕ → ℝ) (C : ℝ)
    (hb : ∀ n, |s (n+1)-4*s n| ≤ C) (N : ℕ) :
    (1/4 : ℝ)^N * limit (fun n => s (n+N)) = limit s := by
  have ht := tendsto_normalized (fun n => s (n+N)) C (fun n => by
    simpa only [Nat.add_assoc, Nat.add_comm 1 N] using hb (n+N))
  have hs := (tendsto_add_atTop_iff_nat N).2 (tendsto_normalized s C hb)
  apply tendsto_nhds_unique (ht.const_mul ((1/4 : ℝ)^N))
  convert hs using 1
  ext n
  simp only [normalized, pow_add]
  ring

/-- Every finite iterate gives a certified asymmetric enclosure of the limit. -/
theorem limit_tail_bounds (s : ℕ → ℝ) (A B : ℝ)
    (hA : ∀ n, A ≤ s (n+1)-4*s n)
    (hB : ∀ n, s (n+1)-4*s n ≤ B) (N : ℕ) :
    normalized s N + (1/4 : ℝ)^N*A/3 ≤ limit s ∧
      limit s ≤ normalized s N + (1/4 : ℝ)^N*B/3 := by
  have hab : ∀ n, |s (n+1)-4*s n| ≤ max |A| |B| := by
    intro n
    rw [abs_le]
    constructor
    · have := neg_abs_le A; have := le_max_left |A| |B|; linarith [hA n]
    · exact (hB n).trans ((le_abs_self B).trans (le_max_right _ _))
  have h := limit_bounds (fun n => s (n+N)) A B
    (fun n => by simpa only [Nat.add_assoc, Nat.add_comm 1 N] using hA (n+N))
    (fun n => by simpa only [Nat.add_assoc, Nat.add_comm 1 N] using hB (n+N))
  have hl := mul_le_mul_of_nonneg_left h.1 (by positivity : 0 ≤ (1/4 : ℝ)^N)
  have hu := mul_le_mul_of_nonneg_left h.2 (by positivity : 0 ≤ (1/4 : ℝ)^N)
  rw [limit_shift s _ hab N] at hl hu
  simp only [Nat.zero_add, normalized] at hl hu ⊢
  constructor <;> nlinarith

/-- Canonical limit for an arbitrary self-map and a real-valued naive height. -/
noncomputable def canonical {X : Type*} (f : X → X) (h : X → ℝ) (x : X) : ℝ :=
  limit (fun n => h (f^[n] x))

/-- The limit satisfies the expected duplication law. This does not assert a
parallelogram or quadratic-form law for an elliptic group. -/
theorem canonical_map {X : Type*} (f : X → X) (h : X → ℝ) (C : ℝ)
    (hb : ∀ x, |h (f x)-4*h x| ≤ C) (x : X) :
    canonical f h (f x) = 4*canonical f h x := by
  have he : (fun n => h (f^[n+1] x)) = (fun n => h (f^[n] (f x))) := by
    funext n
    rw [Function.iterate_succ_apply]
  have hs := limit_shift (fun n => h (f^[n] x)) C
    (fun n => by simpa only [Function.iterate_succ_apply'] using hb (f^[n] x)) 1
  rw [he] at hs
  change (1/4 : ℝ)^1 * canonical f h (f x) = canonical f h x at hs
  norm_num at hs
  linarith

/-- A uniformly bounded change of naive height does not change its normalized limit. -/
theorem limit_eq_of_bounded_difference (s t : ℕ → ℝ) (C D : ℝ)
    (hs : ∀ n, |s (n+1)-4*s n| ≤ C)
    (hd : ∀ n, |t n-s n| ≤ D) : limit t = limit s := by
  have hr : Tendsto (fun n : ℕ => (1/4 : ℝ)^n * D) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (1/4:ℝ) < 1)).mul_const D
  have he : Tendsto (fun n => normalized t n-normalized s n) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ hr
    intro n
    rw [Real.norm_eq_abs]
    have hid : normalized t n-normalized s n = (1/4 : ℝ)^n * (t n-s n) := by
      unfold normalized; ring
    rw [hid, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hd n) (by positivity)
  have ht : Tendsto (normalized t) atTop (𝓝 (limit s)) := by
    convert (tendsto_normalized s C hs).add he using 1 <;> simp
  exact ht.limUnder_eq

/-- Characterization by bounded error and the duplication law. The proof also
establishes convergence from these hypotheses, without presupposing it. -/
theorem canonical_unique {X : Type*} (f : X → X) (h H : X → ℝ) (C : ℝ)
    (hmap : ∀ x, H (f x)=4*H x) (hb : ∀ x, |h x-H x| ≤ C) (x : X) :
    canonical f h x = H x := by
  have hiter (n : ℕ) : H (f^[n] x) = 4^n*H x := by
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', hmap, ih, pow_succ]; ring
  have hid (n : ℕ) : normalized (fun n => H (f^[n] x)) n = H x := by
    rw [normalized, hiter]
    have hpow : (1/4 : ℝ)^n * 4^n = 1 := by rw [← mul_pow]; norm_num
    rw [← mul_assoc, hpow, one_mul]
  have he := limit_eq_of_bounded_difference (fun n => H (f^[n] x))
    (fun n => h (f^[n] x)) 0 C
    (fun n => by rw [Function.iterate_succ_apply', hmap]; simp)
    (fun n => hb (f^[n] x))
  have ht : Tendsto (normalized (fun n => H (f^[n] x))) atTop (𝓝 (H x)) := by
    have hf : normalized (fun n => H (f^[n] x)) = (fun _ => H x) := funext hid
    rw [hf]
    exact tendsto_const_nhds
  exact he.trans ht.limUnder_eq

end LcmSix.CanonicalLimit
