/-
Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
-/
import LcmSix.CanonicalLimit
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic.Abel

/-!
# A bounded parallelogram defect gives a canonical quadratic height

This is the standard limiting argument for heights on an abelian group.
The bounded naive parallelogram defect is an explicit hypothesis: this module
alone does not verify that hypothesis on the four elliptic curves.
The mathematical argument is standard canonical-height theory; see Milne,
*Elliptic Curves*, Chapter IV, Proposition 4.9 and Lemma 4.11. No novelty
claim is made for the limiting or polarization arguments.
-/

namespace LcmSix.CanonicalQuadratic
open Filter
open scoped Topology
variable {A : Type*} [AddCommGroup A]

/-- Group doubling, as opposed to the separately constructed coordinate map. -/
def double (x : A) : A := x + x

lemma iterate_add (n : ℕ) (x y : A) :
    double^[n] (x+y) = double^[n] x + double^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, double]; abel

lemma iterate_sub (n : ℕ) (x y : A) :
    double^[n] (x-y) = double^[n] x - double^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, double]; abel

noncomputable def canonical (h : A → ℝ) : A → ℝ := CanonicalLimit.canonical double h

/-- A uniform approximate parallelogram law; no exact quadraticity is assumed. -/
def BoundedDefect (h : A → ℝ) (C : ℝ) : Prop :=
  ∀ x y, |h (x+y)+h (x-y)-2*h x-2*h y| ≤ C

lemma doubling_defect {h : A → ℝ} {C : ℝ} (hb : BoundedDefect h C) (x : A) :
    |h (double x)-4*h x| ≤ C+|h 0| := by
  have ht := hb x x
  simp only [sub_self] at ht
  have he : h (double x)-4*h x = (h (x+x)+h 0-2*h x-2*h x)-h 0 := by
    dsimp [double]; ring
  rw [he]
  exact (abs_sub _ _).trans (add_le_add ht (le_refl _))

theorem tendsto_height {h : A → ℝ} {C : ℝ} (hb : BoundedDefect h C) (x : A) :
    Tendsto (fun n : ℕ => (1/4:ℝ)^n*h (double^[n] x)) atTop (𝓝 (canonical h x)) :=
  CanonicalLimit.tendsto_normalized _ (C+|h 0|)
    (fun n => by simpa only [Function.iterate_succ_apply'] using doubling_defect hb (double^[n] x))

theorem canonical_double {h : A → ℝ} {C : ℝ} (hb : BoundedDefect h C) (x : A) :
    canonical h (double x) = 4*canonical h x :=
  CanonicalLimit.canonical_map double h (C+|h 0|) (doubling_defect hb) x

/-- Divide the bounded error by 4^n and take the proved limits. -/
theorem parallelogram {h : A → ℝ} {C : ℝ} (hb : BoundedDefect h C) (x y : A) :
    canonical h (x+y)+canonical h (x-y) = 2*canonical h x+2*canonical h y := by
  have hr : Tendsto (fun n : ℕ => (1/4:ℝ)^n*C) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (1/4:ℝ) < 1)).mul_const C
  let e := fun n : ℕ => (1/4:ℝ)^n *
    (h (double^[n] (x+y))+h (double^[n] (x-y))-2*h (double^[n] x)-2*h (double^[n] y))
  have hz : Tendsto e atTop (𝓝 0) := by
    apply squeeze_zero_norm _ hr
    intro n
    dsimp [e]
    rw [abs_mul, abs_of_nonneg (by positivity), iterate_add, iterate_sub]
    exact mul_le_mul_of_nonneg_left (hb _ _) (by positivity)
  have hl : Tendsto e atTop
      (𝓝 (canonical h (x+y)+canonical h (x-y)-2*canonical h x-2*canonical h y)) := by
    convert (((tendsto_height hb (x+y)).add (tendsto_height hb (x-y))).sub
      ((tendsto_height hb x).const_mul 2)).sub ((tendsto_height hb y).const_mul 2) using 1
    ext n
    dsimp [e]
    ring
  have := tendsto_nhds_unique hl hz
  linarith

/-- Algebraic consequences of an exact parallelogram law on any abelian group. -/
def Parallelogram (H : A → ℝ) : Prop :=
  ∀ x y, H (x+y)+H (x-y)=2*H x+2*H y

lemma map_zero {H : A → ℝ} (hp : Parallelogram H) : H 0 = 0 := by
  have := hp 0 0
  simp only [zero_add, sub_zero] at this
  linarith

lemma map_neg {H : A → ℝ} (hp : Parallelogram H) (x : A) : H (-x)=H x := by
  have := hp 0 x
  simp only [zero_add, zero_sub, map_zero hp] at this
  linarith

lemma map_double {H : A → ℝ} (hp : Parallelogram H) (x : A) : H (x+x)=4*H x := by
  have := hp x x
  simp only [sub_self, map_zero hp] at this
  linarith

/-- The symmetric polarization in x-normalized height conventions. -/
noncomputable def pairing (H : A → ℝ) (x y : A) : ℝ := (H (x+y)-H (x-y))/4

lemma pairing_symm {H : A → ℝ} (hp : Parallelogram H) (x y : A) :
    pairing H x y = pairing H y x := by
  have he : y-x = -(x-y) := by abel
  simp only [pairing, add_comm x y, he, map_neg hp]

lemma pairing_neg_left {H : A → ℝ} (hp : Parallelogram H) (x y : A) :
    pairing H (-x) y = -pairing H x y := by
  have h1 : -x+y=-(x-y) := by abel
  have h2 : -x-y=-(x+y) := by abel
  simp only [pairing, h1, h2, map_neg hp]
  ring

lemma pairing_jensen {H : A → ℝ} (hp : Parallelogram H) (x y z : A) :
    pairing H (x+z) y + pairing H (x-z) y = 2*pairing H x y := by
  have h1 := hp (x+y) z
  have h2 := hp (x-y) z
  have e1 : x+z+y=(x+y)+z := by abel
  have e2 : x+z-y=(x-y)+z := by abel
  have e3 : x-z+y=(x+y)-z := by abel
  have e4 : x-z-y=(x-y)-z := by abel
  dsimp [pairing]
  rw [e1,e2,e3,e4]
  linarith

lemma pairing_add_left {H : A → ℝ} (hp : Parallelogram H) (x z y : A) :
    pairing H (x+z) y = pairing H x y + pairing H z y := by
  have h1 := pairing_jensen hp x y z
  have h2 := pairing_jensen hp z y x
  have he : z-x=-(x-z) := by abel
  rw [add_comm z x, he, pairing_neg_left hp] at h2
  linarith

lemma pairing_add_right {H : A → ℝ} (hp : Parallelogram H) (x y z : A) :
    pairing H x (y+z) = pairing H x y + pairing H x z := by
  rw [pairing_symm hp x, pairing_add_left hp, pairing_symm hp y x, pairing_symm hp z x]

lemma pairing_self {H : A → ℝ} (hp : Parallelogram H) (x : A) :
    pairing H x x = H x := by
  simp only [pairing, sub_self, map_zero hp, map_double hp]
  ring

/-- A genuine biadditive pairing, built from the explicit parallelogram premise. -/
noncomputable def bilinear {H : A → ℝ} (hp : Parallelogram H) : A →+ A →+ ℝ where
  toFun x := {
    toFun := pairing H x
    map_zero' := by simp [pairing]
    map_add' := pairing_add_right hp x }
  map_zero' := by
    ext x
    simp [pairing, map_neg hp]
  map_add' x y := by
    ext z
    exact pairing_add_left hp x y z

/-- Integral homogeneity follows from the bilinear pairing, not an assumed law. -/
theorem map_zsmul {H : A → ℝ} (hp : Parallelogram H) (n : ℤ) (x : A) :
    H (n • x) = (n:ℝ)^2*H x := by
  have hleft := (bilinear hp).map_zsmul n x
  have he := DFunLike.congr_fun hleft (n • x)
  simp only [AddMonoidHom.zsmul_apply, zsmul_eq_mul] at he
  change pairing H (n • x) (n • x) = (n:ℝ)*pairing H x (n • x) at he
  have hr := ((bilinear hp) x).map_zsmul n x
  simp only [zsmul_eq_mul] at hr
  change pairing H x (n • x) = (n:ℝ)*pairing H x x at hr
  rw [pairing_self hp, hr, pairing_self hp] at he
  rw [he]
  ring

theorem canonical_zsmul {h : A → ℝ} {C : ℝ} (hb : BoundedDefect h C) (n : ℤ) (x : A) :
    canonical h (n • x) = (n:ℝ)^2*canonical h x :=
  map_zsmul (parallelogram hb) n x

end LcmSix.CanonicalQuadratic
