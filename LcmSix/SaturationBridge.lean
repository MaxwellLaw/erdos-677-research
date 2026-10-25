/-
Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Choose

/-!
# A structural bridge for prime-saturation certificates

Author: MaxwellLaw.

These statements concern an abstract additive group and explicitly supplied
reduction homomorphisms. They certify no particular elliptic-curve reduction,
rank bound, finite-field table, or complete Mordell-Weil basis.
-/

namespace LcmSixSaturation

variable {A E : Type*} [AddCommGroup A] [AddCommGroup E]

/-- A reduction-kernel criterion implies saturation of the generated subgroup
at one natural number `ell`. In applications `ell` is prime, but primality is
not needed for this abstract implication. -/
theorem mem_range_of_nsmul_mem_range
    {ι : Type*} {T : ι → Type*} [∀ i, AddCommGroup (T i)]
    (ell : ℕ) (f : A →+ E) (red : ∀ i, E →+ T i)
    (no_torsion : ∀ x : E, ell • x = 0 → x = 0)
    (kills : ∀ i (x : E), red i (ell • x) = 0)
    (detect : ∀ a : A, (∀ i, red i (f a) = 0) → ∃ b : A, a = ell • b)
    {x : E} (hx : ell • x ∈ f.range) :
    x ∈ f.range := by
  rcases hx with ⟨a, ha⟩
  have hz : ∀ i, red i (f a) = 0 := by
    intro i
    rw [ha]
    exact kills i x
  rcases detect a hz with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  apply sub_eq_zero.mp
  apply no_torsion
  rw [nsmul_sub, ← map_nsmul, ← hb, ha, sub_self]

/-- Coordinatewise vanishing modulo `ell` is exactly the divisibility needed
by the abstract coefficient criterion. This includes arbitrary dimensions. -/
theorem int_vector_divisible_of_mod_zero
    {κ : Type*} (ell : ℕ) (a : κ → ℤ)
    (ha : ∀ j, (a j : ZMod ell) = 0) :
    ∃ b : κ → ℤ, a = ell • b := by
  have hd : ∀ j, (ell : ℤ) ∣ a j := by
    intro j
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a j) ell).mp (ha j)
  choose b hb using hd
  refine ⟨b, ?_⟩
  funext j
  simpa only [Pi.smul_apply, nsmul_eq_mul] using hb j

/-- Joint coefficient detection in finite exponent targets proves saturation.
For the three displayed curve generators, instantiate `κ := Fin 3` and let
`f` be their integer linear-combination homomorphism. The `detect` hypothesis
must be proved from the actual finite reduction certificates. -/
theorem integer_span_saturated_of_joint_reductions
    {κ ι : Type*} {T : ι → Type*} [∀ i, AddCommGroup (T i)]
    (ell : ℕ) (f : (κ → ℤ) →+ E) (red : ∀ i, E →+ T i)
    (no_torsion : ∀ x : E, ell • x = 0 → x = 0)
    (target_exponent : ∀ i (q : T i), ell • q = 0)
    (detect : ∀ a : κ → ℤ, (∀ i, red i (f a) = 0) →
      ∀ j, (a j : ZMod ell) = 0)
    {x : E} (hx : ell • x ∈ f.range) :
    x ∈ f.range := by
  apply mem_range_of_nsmul_mem_range ell f red no_torsion ?_ ?_ hx
  · intro i x
    rw [map_nsmul]
    exact target_exponent i (red i x)
  · intro a ha
    exact int_vector_divisible_of_mod_zero ell a (detect a ha)


end LcmSixSaturation
