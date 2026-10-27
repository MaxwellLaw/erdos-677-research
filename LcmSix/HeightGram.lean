/-
Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
-/
import LcmSix.HeightPoints
import LcmSix.GramCertificates

/-!
# Actual elliptic-group Gram bounds from explicit height intervals

The group law, canonical pairing and Gram expansion are already proved.
This file consumes six explicitly stated numerical height intervals per curve.
Those premises are intentionally retained until the separate logarithm and
orbit certificates prove the intervals; this is not an unconditional
numerical subgroup bound on its own.
-/

namespace LcmSix.HeightGram
open WeierstrassCurve Affine EllipticDuplication EllipticParallelogram

/-- The sum-height polarization agrees with the already defined canonical pairing. -/
theorem pairing_from_sum (M : PrimitiveDynamics.Model)
    [(curve M.a M.b M.c).IsElliptic] (P Q : (curve M.a M.b M.c).Point) :
    canonicalPairing M P Q=
      (canonicalHeight M (P+Q)-canonicalHeight M P-canonicalHeight M Q)/2 := by
  rw [canonicalPairing_apply]
  have h := canonical_parallelogram M P Q
  linarith

/-- Exact six-height expansion for any actual three points and integer coefficients. -/
theorem canonical_three_expansion (M : PrimitiveDynamics.Model)
    [(curve M.a M.b M.c).IsElliptic]
    (P : Fin 3 → (curve M.a M.b M.c).Point) (m : Fin 3 → ℤ) :
    canonicalHeight M (∑ i, m i • P i)=
      canonicalHeight M (P 0)*(m 0 : ℝ)^2+
      canonicalHeight M (P 1)*(m 1 : ℝ)^2+
      canonicalHeight M (P 2)*(m 2 : ℝ)^2+
      (canonicalHeight M (P 0+P 1)-canonicalHeight M (P 0)-canonicalHeight M (P 1))*
        (m 0 : ℝ)*(m 1 : ℝ)+
      (canonicalHeight M (P 0+P 2)-canonicalHeight M (P 0)-canonicalHeight M (P 2))*
        (m 0 : ℝ)*(m 2 : ℝ)+
      (canonicalHeight M (P 1+P 2)-canonicalHeight M (P 1)-canonicalHeight M (P 2))*
        (m 1 : ℝ)*(m 2 : ℝ) := by
  have h := canonical_sum_zsmul M Finset.univ m P
  simp only [Fin.sum_univ_three,canonicalPairing_self] at h
  rw [canonicalPairing_symm M (P 1) (P 0),
    canonicalPairing_symm M (P 2) (P 0),canonicalPairing_symm M (P 2) (P 1)] at h
  simp only [pairing_from_sum] at h
  simp only [Fin.sum_univ_three]
  rw [h]
  ring

namespace Branch1_2

/-- The exact ordered triple whose numerical intervals are being consumed. -/
def basis : Fin 3 →
    (curve PrimitiveDynamics.branch1_2.a PrimitiveDynamics.branch1_2.b
      PrimitiveDynamics.branch1_2.c).Point :=
  ![HeightPoints.Branch1_2.P1,HeightPoints.Branch1_2.P2,HeightPoints.Branch1_2.P3]

/-- Conditional actual-group endpoint: all six height intervals are explicit. -/
theorem lower_of_intervals
    (h_P1 : (69004138032129/140737488355328 : ℝ) ≤ canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.P1 ∧
      canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.P1 ≤ (138285411780399/281474976710656 : ℝ))
    (h_P2 : (499520027231717/281474976710656 : ℝ) ≤ canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.P2 ∧
      canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.P2 ≤ (249898581473929/140737488355328 : ℝ))
    (h_P3 : (327257317279201/281474976710656 : ℝ) ≤ canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.P3 ∧
      canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.P3 ≤ (327534452995343/281474976710656 : ℝ))
    (h_S12 : (291396117684135/281474976710656 : ℝ) ≤ canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.S12 ∧
      canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.S12 ≤ (291673253400277/281474976710656 : ℝ))
    (h_S13 : (542481548340941/281474976710656 : ℝ) ≤ canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.S13 ∧
      canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.S13 ≤ (271379342028541/140737488355328 : ℝ))
    (h_S23 : (133247393536039/70368744177664 : ℝ) ≤ canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.S23 ∧
      canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.S23 ≤ (266633354930149/140737488355328 : ℝ))
    (m : Fin 3 → ℤ) :
    (∑ i, (m i : ℝ)^2)/100 ≤ canonicalHeight PrimitiveDynamics.branch1_2 (∑ i, m i • basis i) := by
  have h := GramBounds.branch1_2_integer_lower
    (canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.P1) (canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.P2) (canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.P3) (canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.S12) (canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.S13) (canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.S23)
    h_P1 h_P2 h_P3 h_S12 h_S13 h_S23 m
  have hs12 : canonicalHeight PrimitiveDynamics.branch1_2 (basis 0+basis 1)=
      canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.S12 :=
    congrArg (canonicalHeight PrimitiveDynamics.branch1_2) HeightPoints.Branch1_2.P1_add_P2
  have hs13 : canonicalHeight PrimitiveDynamics.branch1_2 (basis 0+basis 2)=
      canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.S13 :=
    congrArg (canonicalHeight PrimitiveDynamics.branch1_2) HeightPoints.Branch1_2.P1_add_P3
  have hs23 : canonicalHeight PrimitiveDynamics.branch1_2 (basis 1+basis 2)=
      canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.S23 :=
    congrArg (canonicalHeight PrimitiveDynamics.branch1_2) HeightPoints.Branch1_2.P2_add_P3
  rw [canonical_three_expansion PrimitiveDynamics.branch1_2 basis m,hs12,hs13,hs23]
  simpa [basis,Fin.sum_univ_three] using h

end Branch1_2

namespace Branch1_5

/-- The exact ordered triple whose numerical intervals are being consumed. -/
def basis : Fin 3 →
    (curve PrimitiveDynamics.branch1_5.a PrimitiveDynamics.branch1_5.b
      PrimitiveDynamics.branch1_5.c).Point :=
  ![HeightPoints.Branch1_5.P1,HeightPoints.Branch1_5.P2,HeightPoints.Branch1_5.P3]

/-- Conditional actual-group endpoint: all six height intervals are explicit. -/
theorem lower_of_intervals
    (h_P1 : (181869775642269/281474976710656 : ℝ) ≤ canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.P1 ∧
      canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.P1 ≤ (45568291910769/70368744177664 : ℝ))
    (h_P2 : (674117094805055/281474976710656 : ℝ) ≤ canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.P2 ∧
      canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.P2 ≤ (674520486805863/281474976710656 : ℝ))
    (h_P3 : (453154414702007/140737488355328 : ℝ) ≤ canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.P3 ∧
      canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.P3 ≤ (453356110702411/140737488355328 : ℝ))
    (h_S12 : (603074254015333/140737488355328 : ℝ) ≤ canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.S12 ∧
      canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.S12 ≤ (603275950015737/140737488355328 : ℝ))
    (h_S13 : (1724507484655291/281474976710656 : ℝ) ≤ canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.S13 ∧
      canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.S13 ≤ (1724910876656099/281474976710656 : ℝ))
    (h_S23 : (2575221726216083/281474976710656 : ℝ) ≤ canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.S23 ∧
      canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.S23 ≤ (1287812559108445/140737488355328 : ℝ))
    (m : Fin 3 → ℤ) :
    (∑ i, (m i : ℝ)^2)/100 ≤ canonicalHeight PrimitiveDynamics.branch1_5 (∑ i, m i • basis i) := by
  have h := GramBounds.branch1_5_integer_lower
    (canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.P1) (canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.P2) (canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.P3) (canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.S12) (canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.S13) (canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.S23)
    h_P1 h_P2 h_P3 h_S12 h_S13 h_S23 m
  have hs12 : canonicalHeight PrimitiveDynamics.branch1_5 (basis 0+basis 1)=
      canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.S12 :=
    congrArg (canonicalHeight PrimitiveDynamics.branch1_5) HeightPoints.Branch1_5.P1_add_P2
  have hs13 : canonicalHeight PrimitiveDynamics.branch1_5 (basis 0+basis 2)=
      canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.S13 :=
    congrArg (canonicalHeight PrimitiveDynamics.branch1_5) HeightPoints.Branch1_5.P1_add_P3
  have hs23 : canonicalHeight PrimitiveDynamics.branch1_5 (basis 1+basis 2)=
      canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.S23 :=
    congrArg (canonicalHeight PrimitiveDynamics.branch1_5) HeightPoints.Branch1_5.P2_add_P3
  rw [canonical_three_expansion PrimitiveDynamics.branch1_5 basis m,hs12,hs13,hs23]
  simpa [basis,Fin.sum_univ_three] using h

end Branch1_5

namespace Branch1_10

/-- The exact ordered triple whose numerical intervals are being consumed. -/
def basis : Fin 3 →
    (curve PrimitiveDynamics.branch1_10.a PrimitiveDynamics.branch1_10.b
      PrimitiveDynamics.branch1_10.c).Point :=
  ![HeightPoints.Branch1_10.P1,HeightPoints.Branch1_10.P2,HeightPoints.Branch1_10.P3]

/-- Conditional actual-group endpoint: all six height intervals are explicit. -/
theorem lower_of_intervals
    (h_P1 : (173846524985651/35184372088832 : ℝ) ≤ canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.P1 ∧
      canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.P1 ≤ (695633705718799/140737488355328 : ℝ))
    (h_P2 : (24560193892887/8796093022208 : ℝ) ≤ canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.P2 ∧
      canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.P2 ≤ (393210708062387/140737488355328 : ℝ))
    (h_P3 : (683068736564691/281474976710656 : ℝ) ≤ canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.P3 ∧
      canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.P3 ≤ (683563948117081/281474976710656 : ℝ))
    (h_S12 : (403438511068675/140737488355328 : ℝ) ≤ canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.S12 ∧
      canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.S12 ≤ (201843058422435/70368744177664 : ℝ))
    (h_S13 : (2639177818358167/281474976710656 : ℝ) ≤ canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.S13 ∧
      canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.S13 ≤ (2639673029910557/281474976710656 : ℝ))
    (h_S23 : (2204799160196033/281474976710656 : ℝ) ≤ canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.S23 ∧
      canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.S23 ≤ (2205294371748423/281474976710656 : ℝ))
    (m : Fin 3 → ℤ) :
    (∑ i, (m i : ℝ)^2)/100 ≤ canonicalHeight PrimitiveDynamics.branch1_10 (∑ i, m i • basis i) := by
  have h := GramBounds.branch1_10_integer_lower
    (canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.P1) (canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.P2) (canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.P3) (canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.S12) (canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.S13) (canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.S23)
    h_P1 h_P2 h_P3 h_S12 h_S13 h_S23 m
  have hs12 : canonicalHeight PrimitiveDynamics.branch1_10 (basis 0+basis 1)=
      canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.S12 :=
    congrArg (canonicalHeight PrimitiveDynamics.branch1_10) HeightPoints.Branch1_10.P1_add_P2
  have hs13 : canonicalHeight PrimitiveDynamics.branch1_10 (basis 0+basis 2)=
      canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.S13 :=
    congrArg (canonicalHeight PrimitiveDynamics.branch1_10) HeightPoints.Branch1_10.P1_add_P3
  have hs23 : canonicalHeight PrimitiveDynamics.branch1_10 (basis 1+basis 2)=
      canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.S23 :=
    congrArg (canonicalHeight PrimitiveDynamics.branch1_10) HeightPoints.Branch1_10.P2_add_P3
  rw [canonical_three_expansion PrimitiveDynamics.branch1_10 basis m,hs12,hs13,hs23]
  simpa [basis,Fin.sum_univ_three] using h

end Branch1_10

namespace Branch2_5

/-- The exact ordered triple whose numerical intervals are being consumed. -/
def basis : Fin 3 →
    (curve PrimitiveDynamics.branch2_5.a PrimitiveDynamics.branch2_5.b
      PrimitiveDynamics.branch2_5.c).Point :=
  ![HeightPoints.Branch2_5.P1,HeightPoints.Branch2_5.P2,HeightPoints.Branch2_5.P3]

/-- Conditional actual-group endpoint: all six height intervals are explicit. -/
theorem lower_of_intervals
    (h_P1 : (88326205004897/140737488355328 : ℝ) ≤ canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.P1 ∧
      canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.P1 ≤ (177113449569131/281474976710656 : ℝ))
    (h_P2 : (152173520262289/70368744177664 : ℝ) ≤ canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.P2 ∧
      canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.P2 ≤ (609155120608493/281474976710656 : ℝ))
    (h_P3 : (614722085831731/281474976710656 : ℝ) ≤ canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.P3 ∧
      canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.P3 ≤ (153795781347767/70368744177664 : ℝ))
    (h_S12 : (406667052853497/281474976710656 : ℝ) ≤ canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.S12 ∧
      canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.S12 ≤ (203564046206417/140737488355328 : ℝ))
    (h_S13 : (601802321280363/140737488355328 : ℝ) ≤ canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.S13 ∧
      canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.S13 ≤ (1204065682120063/281474976710656 : ℝ))
    (h_S23 : (1001212437183885/281474976710656 : ℝ) ≤ canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.S23 ∧
      canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.S23 ≤ (500836738371611/140737488355328 : ℝ))
    (m : Fin 3 → ℤ) :
    (∑ i, (m i : ℝ)^2)/100 ≤ canonicalHeight PrimitiveDynamics.branch2_5 (∑ i, m i • basis i) := by
  have h := GramBounds.branch2_5_integer_lower
    (canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.P1) (canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.P2) (canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.P3) (canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.S12) (canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.S13) (canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.S23)
    h_P1 h_P2 h_P3 h_S12 h_S13 h_S23 m
  have hs12 : canonicalHeight PrimitiveDynamics.branch2_5 (basis 0+basis 1)=
      canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.S12 :=
    congrArg (canonicalHeight PrimitiveDynamics.branch2_5) HeightPoints.Branch2_5.P1_add_P2
  have hs13 : canonicalHeight PrimitiveDynamics.branch2_5 (basis 0+basis 2)=
      canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.S13 :=
    congrArg (canonicalHeight PrimitiveDynamics.branch2_5) HeightPoints.Branch2_5.P1_add_P3
  have hs23 : canonicalHeight PrimitiveDynamics.branch2_5 (basis 1+basis 2)=
      canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.S23 :=
    congrArg (canonicalHeight PrimitiveDynamics.branch2_5) HeightPoints.Branch2_5.P2_add_P3
  rw [canonical_three_expansion PrimitiveDynamics.branch2_5 basis m,hs12,hs13,hs23]
  simpa [basis,Fin.sum_univ_three] using h

end Branch2_5

end LcmSix.HeightGram
