/-
Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
-/
import LcmSix.EllipticParallelogram

/-!
Actual rational points and pairwise sums used by the fixed height certificate.
Uses Mathlib's point group and chord formula (David Kurniadi Angdinata).
-/

namespace LcmSix.HeightPoints
open WeierstrassCurve Affine EllipticDuplication

/-- Construct an actual nonsingular point from its exact curve equation. -/
def point (a b c x y : ℚ) [(curve a b c).IsElliptic]
    (h : y^2=x^3+a*x^2+b*x+c) : (curve a b c).Point :=
  Point.mk ((EllipticDuplication.equation_iff a b c x y).mpr h)

theorem point_xRep (a b c x y : ℚ) [(curve a b c).IsElliptic]
    (h : y^2=x^3+a*x^2+b*x+c) :
    (point a b c x y h).xRep = ![x,1] := rfl

namespace Branch1_2

def P1 : (curve (-1) (-65) (261)).Point :=
  point (-1) (-65) (261) (5) (6) (by norm_num)

theorem P1_xRep : P1.xRep = ![(5 : ℚ),1] := rfl

def P2 : (curve (-1) (-65) (261)).Point :=
  point (-1) (-65) (261) (13) (38) (by norm_num)

theorem P2_xRep : P2.xRep = ![(13 : ℚ),1] := rfl

def P3 : (curve (-1) (-65) (261)).Point :=
  point (-1) (-65) (261) (-7) (18) (by norm_num)

theorem P3_xRep : P3.xRep = ![(-7 : ℚ),1] := rfl

def S12 : (curve (-1) (-65) (261)).Point :=
  point (-1) (-65) (261) (-1) (18) (by norm_num)

theorem S12_xRep : S12.xRep = ![(-1 : ℚ),1] := rfl

def S13 : (curve (-1) (-65) (261)).Point :=
  point (-1) (-65) (261) (4) (-7) (by norm_num)

theorem S13_xRep : S13.xRep = ![(4 : ℚ),1] := rfl

def S23 : (curve (-1) (-65) (261)).Point :=
  point (-1) (-65) (261) (-4) (-21) (by norm_num)

theorem S23_xRep : S23.xRep = ![(-4 : ℚ),1] := rfl

theorem P1_add_P2 : P1+P2=S12 := by
  unfold P1 P2 S12 point Point.mk
  rw [Point.add_of_X_ne (by norm_num)]
  rw [Point.some.injEq]
  norm_num [slope_of_X_ne,addX,addY,negAddY,negY,curve]

theorem P1_add_P3 : P1+P3=S13 := by
  unfold P1 P3 S13 point Point.mk
  rw [Point.add_of_X_ne (by norm_num)]
  rw [Point.some.injEq]
  norm_num [slope_of_X_ne,addX,addY,negAddY,negY,curve]

theorem P2_add_P3 : P2+P3=S23 := by
  unfold P2 P3 S23 point Point.mk
  rw [Point.add_of_X_ne (by norm_num)]
  rw [Point.some.injEq]
  norm_num [slope_of_X_ne,addX,addY,negAddY,negY,curve]

end Branch1_2

namespace Branch1_5

def P1 : (curve (-1) (-408) (6912)).Point :=
  point (-1) (-408) (6912) (12) (-60) (by norm_num)

theorem P1_xRep : P1.xRep = ![(12 : ℚ),1] := rfl

def P2 : (curve (-1) (-408) (6912)).Point :=
  point (-1) (-408) (6912) (-4) (92) (by norm_num)

theorem P2_xRep : P2.xRep = ![(-4 : ℚ),1] := rfl

def P3 : (curve (-1) (-408) (6912)).Point :=
  point (-1) (-408) (6912) (78) (-666) (by norm_num)

theorem P3_xRep : P3.xRep = ![(78 : ℚ),1] := rfl

def S12 : (curve (-1) (-408) (6912)).Point :=
  point (-1) (-408) (6912) (333/4) (5895/8) (by norm_num)

theorem S12_xRep : S12.xRep = ![(333/4 : ℚ),1] := rfl

def S13 : (curve (-1) (-408) (6912)).Point :=
  point (-1) (-408) (6912) (-568/121) (-124160/1331) (by norm_num)

theorem S13_xRep : S13.xRep = ![(-568/121 : ℚ),1] := rfl

def S23 : (curve (-1) (-408) (6912)).Point :=
  point (-1) (-408) (6912) (20928/1681) (4139376/68921) (by norm_num)

theorem S23_xRep : S23.xRep = ![(20928/1681 : ℚ),1] := rfl

theorem P1_add_P2 : P1+P2=S12 := by
  unfold P1 P2 S12 point Point.mk
  rw [Point.add_of_X_ne (by norm_num)]
  rw [Point.some.injEq]
  norm_num [slope_of_X_ne,addX,addY,negAddY,negY,curve]

theorem P1_add_P3 : P1+P3=S13 := by
  unfold P1 P3 S13 point Point.mk
  rw [Point.add_of_X_ne (by norm_num)]
  rw [Point.some.injEq]
  norm_num [slope_of_X_ne,addX,addY,negAddY,negY,curve]

theorem P2_add_P3 : P2+P3=S23 := by
  unfold P2 P3 S23 point Point.mk
  rw [Point.add_of_X_ne (by norm_num)]
  rw [Point.some.injEq]
  norm_num [slope_of_X_ne,addX,addY,negAddY,negY,curve]

end Branch1_5

namespace Branch1_10

def P1 : (curve (1) (-1633) (97763)).Point :=
  point (1) (-1633) (97763) (221/4) (3387/8) (by norm_num)

theorem P1_xRep : P1.xRep = ![(221/4 : ℚ),1] := rfl

def P2 : (curve (1) (-1633) (97763)).Point :=
  point (1) (-1633) (97763) (14) (279) (by norm_num)

theorem P2_xRep : P2.xRep = ![(14 : ℚ),1] := rfl

def P3 : (curve (1) (-1633) (97763)).Point :=
  point (1) (-1633) (97763) (43) (330) (by norm_num)

theorem P3_xRep : P3.xRep = ![(43 : ℚ),1] := rfl

def S12 : (curve (1) (-1633) (97763)).Point :=
  point (1) (-1633) (97763) (-58) (-27) (by norm_num)

theorem S12_xRep : S12.xRep = ![(-58 : ℚ),1] := rfl

def S13 : (curve (1) (-1633) (97763)).Point :=
  point (1) (-1633) (97763) (-98797/2401) (36637770/117649) (by norm_num)

theorem S13_xRep : S13.xRep = ![(-98797/2401 : ℚ),1] := rfl

def S23 : (curve (1) (-1633) (97763)).Point :=
  point (1) (-1633) (97763) (-46177/841) (-3849030/24389) (by norm_num)

theorem S23_xRep : S23.xRep = ![(-46177/841 : ℚ),1] := rfl

theorem P1_add_P2 : P1+P2=S12 := by
  unfold P1 P2 S12 point Point.mk
  rw [Point.add_of_X_ne (by norm_num)]
  rw [Point.some.injEq]
  norm_num [slope_of_X_ne,addX,addY,negAddY,negY,curve]

theorem P1_add_P3 : P1+P3=S13 := by
  unfold P1 P3 S13 point Point.mk
  rw [Point.add_of_X_ne (by norm_num)]
  rw [Point.some.injEq]
  norm_num [slope_of_X_ne,addX,addY,negAddY,negY,curve]

theorem P2_add_P3 : P2+P3=S23 := by
  unfold P2 P3 S23 point Point.mk
  rw [Point.add_of_X_ne (by norm_num)]
  rw [Point.some.injEq]
  norm_num [slope_of_X_ne,addX,addY,negAddY,negY,curve]

end Branch1_10

namespace Branch2_5

def P1 : (curve (1) (-1633) (32963)).Point :=
  point (1) (-1633) (32963) (23) (-90) (by norm_num)

theorem P1_xRep : P1.xRep = ![(23 : ℚ),1] := rfl

def P2 : (curve (1) (-1633) (32963)).Point :=
  point (1) (-1633) (32963) (17) (-102) (by norm_num)

theorem P2_xRep : P2.xRep = ![(17 : ℚ),1] := rfl

def P3 : (curve (1) (-1633) (32963)).Point :=
  point (1) (-1633) (32963) (-1) (186) (by norm_num)

theorem P3_xRep : P3.xRep = ![(-1 : ℚ),1] := rfl

def S12 : (curve (1) (-1633) (32963)).Point :=
  point (1) (-1633) (32963) (-37) (210) (by norm_num)

theorem S12_xRep : S12.xRep = ![(-37 : ℚ),1] := rfl

def S13 : (curve (1) (-1633) (32963)).Point :=
  point (1) (-1633) (32963) (437/4) (8655/8) (by norm_num)

theorem S13_xRep : S13.xRep = ![(437/4 : ℚ),1] := rfl

def S23 : (curve (1) (-1633) (32963)).Point :=
  point (1) (-1633) (32963) (239) (3654) (by norm_num)

theorem S23_xRep : S23.xRep = ![(239 : ℚ),1] := rfl

theorem P1_add_P2 : P1+P2=S12 := by
  unfold P1 P2 S12 point Point.mk
  rw [Point.add_of_X_ne (by norm_num)]
  rw [Point.some.injEq]
  norm_num [slope_of_X_ne,addX,addY,negAddY,negY,curve]

theorem P1_add_P3 : P1+P3=S13 := by
  unfold P1 P3 S13 point Point.mk
  rw [Point.add_of_X_ne (by norm_num)]
  rw [Point.some.injEq]
  norm_num [slope_of_X_ne,addX,addY,negAddY,negY,curve]

theorem P2_add_P3 : P2+P3=S23 := by
  unfold P2 P3 S23 point Point.mk
  rw [Point.add_of_X_ne (by norm_num)]
  rw [Point.some.injEq]
  norm_num [slope_of_X_ne,addX,addY,negAddY,negY,curve]

end Branch2_5

end LcmSix.HeightPoints
