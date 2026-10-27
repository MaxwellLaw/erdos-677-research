/-
Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
-/
import LcmSix.HeightEnclosure
import LcmSix.HeightOrbits
import LcmSix.LogCertificates

/-!
# Actual canonical-height intervals for all 24 certificate points
Every orbit, primitivity, logarithm and finite rounding premise is discharged.
These are the original saved N=7 intervals, not assumed numerical hypotheses.
-/
namespace LcmSix.HeightIntervals
open EllipticDuplication HeightEnclosure

theorem Branch1_2_P1_height : ((69004138032129/140737488355328):ℝ)≤canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.P1 ∧
    canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.P1≤((138285411780399/281474976710656):ℝ) := by
  apply from_seven_steps PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.P1
    (HeightOrbits.Branch1_2.P1.B:ℝ) 138994166307188736 (566207792126145687/70368744177664) (2264831168504582749/281474976710656) (2511054316420297/281474976710656) (5555360201652237/140737488355328) (69004138032129/140737488355328) (138285411780399/281474976710656)
  · exact HeightOrbits.Branch1_2.P1.height7
  · norm_num [PrimitiveDynamics.branch1_2]
  · simpa only [LogCertificates.Branch1_2_P1_size,HeightOrbits.Branch1_2.P1.B,
      Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,Int.cast_ofNat] using LogCertificates.Branch1_2_P1_log
  · change Real.log (7488:ℝ)≤((2511054316420297/281474976710656):ℝ)
    simpa only [LogCertificates.Branch1_2_C_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_2_C_log.2
  · simpa only [LogCertificates.Branch1_2_D_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_2_D_log.2
  · norm_num
  · norm_num

theorem Branch1_2_P2_height : ((499520027231717/281474976710656):ℝ)≤canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.P2 ∧
    canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.P2≤((249898581473929/140737488355328):ℝ) := by
  apply from_seven_steps PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.P2
    (HeightOrbits.Branch1_2.P2.B:ℝ) 138994166307188736 (8187839699632225557/281474976710656) (4093919849816112779/140737488355328) (2511054316420297/281474976710656) (5555360201652237/140737488355328) (499520027231717/281474976710656) (249898581473929/140737488355328)
  · exact HeightOrbits.Branch1_2.P2.height7
  · norm_num [PrimitiveDynamics.branch1_2]
  · simpa only [LogCertificates.Branch1_2_P2_size,HeightOrbits.Branch1_2.P2.B,
      Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,Int.cast_ofNat] using LogCertificates.Branch1_2_P2_log
  · change Real.log (7488:ℝ)≤((2511054316420297/281474976710656):ℝ)
    simpa only [LogCertificates.Branch1_2_C_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_2_C_log.2
  · simpa only [LogCertificates.Branch1_2_D_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_2_D_log.2
  · norm_num
  · norm_num

theorem Branch1_2_P3_height : ((327257317279201/281474976710656):ℝ)≤canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.P3 ∧
    canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.P3≤((327534452995343/281474976710656):ℝ) := by
  apply from_seven_steps PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.P3
    (HeightOrbits.Branch1_2.P3.B:ℝ) 138994166307188736 (2682743729885106541/140737488355328) (5365487459770213083/281474976710656) (2511054316420297/281474976710656) (5555360201652237/140737488355328) (327257317279201/281474976710656) (327534452995343/281474976710656)
  · exact HeightOrbits.Branch1_2.P3.height7
  · norm_num [PrimitiveDynamics.branch1_2]
  · simpa only [LogCertificates.Branch1_2_P3_size,HeightOrbits.Branch1_2.P3.B,
      Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,Int.cast_ofNat] using LogCertificates.Branch1_2_P3_log
  · change Real.log (7488:ℝ)≤((2511054316420297/281474976710656):ℝ)
    simpa only [LogCertificates.Branch1_2_C_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_2_C_log.2
  · simpa only [LogCertificates.Branch1_2_D_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_2_D_log.2
  · norm_num
  · norm_num

theorem Branch1_2_S12_height : ((291396117684135/281474976710656):ℝ)≤canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.S12 ∧
    canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.S12≤((291673253400277/281474976710656):ℝ) := by
  apply from_seven_steps PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.S12
    (HeightOrbits.Branch1_2.S12.B:ℝ) 138994166307188736 (597242195700581275/35184372088832) (4777937565604650201/281474976710656) (2511054316420297/281474976710656) (5555360201652237/140737488355328) (291396117684135/281474976710656) (291673253400277/281474976710656)
  · exact HeightOrbits.Branch1_2.S12.height7
  · norm_num [PrimitiveDynamics.branch1_2]
  · simpa only [LogCertificates.Branch1_2_S12_size,HeightOrbits.Branch1_2.S12.B,
      Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,Int.cast_ofNat] using LogCertificates.Branch1_2_S12_log
  · change Real.log (7488:ℝ)≤((2511054316420297/281474976710656):ℝ)
    simpa only [LogCertificates.Branch1_2_C_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_2_C_log.2
  · simpa only [LogCertificates.Branch1_2_D_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_2_D_log.2
  · norm_num
  · norm_num

theorem Branch1_2_S13_height : ((542481548340941/281474976710656):ℝ)≤canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.S13 ∧
    canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.S13≤((271379342028541/140737488355328):ℝ) := by
  apply from_seven_steps PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.S13
    (HeightOrbits.Branch1_2.S13.B:ℝ) 138994166307188736 (1111465157685718199/35184372088832) (8891721261485745593/281474976710656) (2511054316420297/281474976710656) (5555360201652237/140737488355328) (542481548340941/281474976710656) (271379342028541/140737488355328)
  · exact HeightOrbits.Branch1_2.S13.height7
  · norm_num [PrimitiveDynamics.branch1_2]
  · simpa only [LogCertificates.Branch1_2_S13_size,HeightOrbits.Branch1_2.S13.B,
      Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,Int.cast_ofNat] using LogCertificates.Branch1_2_S13_log
  · change Real.log (7488:ℝ)≤((2511054316420297/281474976710656):ℝ)
    simpa only [LogCertificates.Branch1_2_C_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_2_C_log.2
  · simpa only [LogCertificates.Branch1_2_D_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_2_D_log.2
  · norm_num
  · norm_num

theorem Branch1_2_S23_height : ((133247393536039/70368744177664):ℝ)≤canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.S23 ∧
    canonicalHeight PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.S23≤((266633354930149/140737488355328):ℝ) := by
  apply from_seven_steps PrimitiveDynamics.branch1_2 HeightPoints.Branch1_2.S23
    (HeightOrbits.Branch1_2.S23.B:ℝ) 138994166307188736 (4368102378122817163/140737488355328) (8736204756245634327/281474976710656) (2511054316420297/281474976710656) (5555360201652237/140737488355328) (133247393536039/70368744177664) (266633354930149/140737488355328)
  · exact HeightOrbits.Branch1_2.S23.height7
  · norm_num [PrimitiveDynamics.branch1_2]
  · simpa only [LogCertificates.Branch1_2_S23_size,HeightOrbits.Branch1_2.S23.B,
      Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,Int.cast_ofNat] using LogCertificates.Branch1_2_S23_log
  · change Real.log (7488:ℝ)≤((2511054316420297/281474976710656):ℝ)
    simpa only [LogCertificates.Branch1_2_C_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_2_C_log.2
  · simpa only [LogCertificates.Branch1_2_D_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_2_D_log.2
  · norm_num
  · norm_num

theorem Branch1_5_P1_height : ((181869775642269/281474976710656):ℝ)≤canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.P1 ∧
    canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.P1≤((45568291910769/70368744177664):ℝ) := by
  apply from_seven_steps PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.P1
    (HeightOrbits.Branch1_5.P1.B:ℝ) 15632567065268860354560000 (2985197323146460663/281474976710656) (373149665393307583/35184372088832) (874691638272127/70368744177664) (16328757070570205/281474976710656) (181869775642269/281474976710656) (45568291910769/70368744177664)
  · exact HeightOrbits.Branch1_5.P1.height7
  · norm_num [PrimitiveDynamics.branch1_5]
  · simpa only [LogCertificates.Branch1_5_P1_size,HeightOrbits.Branch1_5.P1.B,
      Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,Int.cast_ofNat] using LogCertificates.Branch1_5_P1_log
  · change Real.log (250225:ℝ)≤((874691638272127/70368744177664):ℝ)
    simpa only [LogCertificates.Branch1_5_C_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_5_C_log.2
  · simpa only [LogCertificates.Branch1_5_D_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_5_D_log.2
  · norm_num
  · norm_num

theorem Branch1_5_P2_height : ((674117094805055/281474976710656):ℝ)≤canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.P2 ∧
    canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.P2≤((674520486805863/281474976710656):ℝ) := by
  apply from_seven_steps PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.P2
    (HeightOrbits.Branch1_5.P2.B:ℝ) 15632567065268860354560000 (11050177400309547523/281474976710656) (2762544350077386881/70368744177664) (874691638272127/70368744177664) (16328757070570205/281474976710656) (674117094805055/281474976710656) (674520486805863/281474976710656)
  · exact HeightOrbits.Branch1_5.P2.height7
  · norm_num [PrimitiveDynamics.branch1_5]
  · simpa only [LogCertificates.Branch1_5_P2_size,HeightOrbits.Branch1_5.P2.B,
      Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,Int.cast_ofNat] using LogCertificates.Branch1_5_P2_log
  · change Real.log (250225:ℝ)≤((874691638272127/70368744177664):ℝ)
    simpa only [LogCertificates.Branch1_5_C_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_5_C_log.2
  · simpa only [LogCertificates.Branch1_5_D_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_5_D_log.2
  · norm_num
  · norm_num

theorem Branch1_5_P3_height : ((453154414702007/140737488355328):ℝ)≤canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.P3 ∧
    canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.P3≤((453356110702411/140737488355328):ℝ) := by
  apply from_seven_steps PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.P3
    (HeightOrbits.Branch1_5.P3.B:ℝ) 15632567065268860354560000 (14854406779978894579/281474976710656) (3713601694994723645/70368744177664) (874691638272127/70368744177664) (16328757070570205/281474976710656) (453154414702007/140737488355328) (453356110702411/140737488355328)
  · exact HeightOrbits.Branch1_5.P3.height7
  · norm_num [PrimitiveDynamics.branch1_5]
  · simpa only [LogCertificates.Branch1_5_P3_size,HeightOrbits.Branch1_5.P3.B,
      Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,Int.cast_ofNat] using LogCertificates.Branch1_5_P3_log
  · change Real.log (250225:ℝ)≤((874691638272127/70368744177664):ℝ)
    simpa only [LogCertificates.Branch1_5_C_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_5_C_log.2
  · simpa only [LogCertificates.Branch1_5_D_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_5_D_log.2
  · norm_num
  · norm_num

theorem Branch1_5_S12_height : ((603074254015333/140737488355328):ℝ)≤canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.S12 ∧
    canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.S12≤((603275950015737/140737488355328):ℝ) := by
  apply from_seven_steps PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.S12
    (HeightOrbits.Branch1_5.S12.B:ℝ) 15632567065268860354560000 (19766980074597962079/281474976710656) (617718127331186315/8796093022208) (874691638272127/70368744177664) (16328757070570205/281474976710656) (603074254015333/140737488355328) (603275950015737/140737488355328)
  · exact HeightOrbits.Branch1_5.S12.height7
  · norm_num [PrimitiveDynamics.branch1_5]
  · simpa only [LogCertificates.Branch1_5_S12_size,HeightOrbits.Branch1_5.S12.B,
      Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,Int.cast_ofNat] using LogCertificates.Branch1_5_S12_log
  · change Real.log (250225:ℝ)≤((874691638272127/70368744177664):ℝ)
    simpa only [LogCertificates.Branch1_5_C_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_5_C_log.2
  · simpa only [LogCertificates.Branch1_5_D_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_5_D_log.2
  · norm_num
  · norm_num

theorem Branch1_5_S13_height : ((1724507484655291/281474976710656):ℝ)≤canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.S13 ∧
    canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.S13≤((1724910876656099/281474976710656):ℝ) := by
  apply from_seven_steps PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.S13
    (HeightOrbits.Branch1_5.S13.B:ℝ) 15632567065268860354560000 (1766235846725988615/17592186044416) (28259773547615817841/281474976710656) (874691638272127/70368744177664) (16328757070570205/281474976710656) (1724507484655291/281474976710656) (1724910876656099/281474976710656)
  · exact HeightOrbits.Branch1_5.S13.height7
  · norm_num [PrimitiveDynamics.branch1_5]
  · simpa only [LogCertificates.Branch1_5_S13_size,HeightOrbits.Branch1_5.S13.B,
      Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,Int.cast_ofNat] using LogCertificates.Branch1_5_S13_log
  · change Real.log (250225:ℝ)≤((874691638272127/70368744177664):ℝ)
    simpa only [LogCertificates.Branch1_5_C_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_5_C_log.2
  · simpa only [LogCertificates.Branch1_5_D_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_5_D_log.2
  · norm_num
  · norm_num

theorem Branch1_5_S23_height : ((2575221726216083/281474976710656):ℝ)≤canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.S23 ∧
    canonicalHeight PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.S23≤((1287812559108445/140737488355328):ℝ) := by
  apply from_seven_steps PrimitiveDynamics.branch1_5 HeightPoints.Branch1_5.S23
    (HeightOrbits.Branch1_5.S23.B:ℝ) 15632567065268860354560000 (1318683615042119651/8796093022208) (42197875681347828833/281474976710656) (874691638272127/70368744177664) (16328757070570205/281474976710656) (2575221726216083/281474976710656) (1287812559108445/140737488355328)
  · exact HeightOrbits.Branch1_5.S23.height7
  · norm_num [PrimitiveDynamics.branch1_5]
  · simpa only [LogCertificates.Branch1_5_S23_size,HeightOrbits.Branch1_5.S23.B,
      Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,Int.cast_ofNat] using LogCertificates.Branch1_5_S23_log
  · change Real.log (250225:ℝ)≤((874691638272127/70368744177664):ℝ)
    simpa only [LogCertificates.Branch1_5_C_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_5_C_log.2
  · simpa only [LogCertificates.Branch1_5_D_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_5_D_log.2
  · norm_num
  · norm_num

theorem Branch1_10_P1_height : ((173846524985651/35184372088832):ℝ)≤canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.P1 ∧
    canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.P1≤((695633705718799/140737488355328):ℝ) := by
  apply from_seven_steps PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.P1
    (HeightOrbits.Branch1_10.P1.B:ℝ) 11745976358580478445504632320000 (11396562031324983735/140737488355328) (22793124062649967471/281474976710656) (4203619030873145/281474976710656) (20137019192144165/281474976710656) (173846524985651/35184372088832) (695633705718799/140737488355328)
  · exact HeightOrbits.Branch1_10.P1.height7
  · norm_num [PrimitiveDynamics.branch1_10]
  · simpa only [LogCertificates.Branch1_10_P1_size,HeightOrbits.Branch1_10.P1.B,
      Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,Int.cast_ofNat] using LogCertificates.Branch1_10_P1_log
  · change Real.log (3061008:ℝ)≤((4203619030873145/281474976710656):ℝ)
    simpa only [LogCertificates.Branch1_10_C_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_10_C_log.2
  · simpa only [LogCertificates.Branch1_10_D_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_10_D_log.2
  · norm_num
  · norm_num

theorem Branch1_10_P2_height : ((24560193892887/8796093022208):ℝ)≤canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.P2 ∧
    canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.P2≤((393210708062387/140737488355328):ℝ) := by
  apply from_seven_steps PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.P2
    (HeightOrbits.Branch1_10.P2.B:ℝ) 11745976358580478445504632320000 (12883327275444664323/281474976710656) (3220831818861166081/70368744177664) (4203619030873145/281474976710656) (20137019192144165/281474976710656) (24560193892887/8796093022208) (393210708062387/140737488355328)
  · exact HeightOrbits.Branch1_10.P2.height7
  · norm_num [PrimitiveDynamics.branch1_10]
  · simpa only [LogCertificates.Branch1_10_P2_size,HeightOrbits.Branch1_10.P2.B,
      Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,Int.cast_ofNat] using LogCertificates.Branch1_10_P2_log
  · change Real.log (3061008:ℝ)≤((4203619030873145/281474976710656):ℝ)
    simpa only [LogCertificates.Branch1_10_C_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_10_C_log.2
  · simpa only [LogCertificates.Branch1_10_D_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_10_D_log.2
  · norm_num
  · norm_num

theorem Branch1_10_P3_height : ((683068736564691/281474976710656):ℝ)≤canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.P3 ∧
    canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.P3≤((683563948117081/281474976710656):ℝ) := by
  apply from_seven_steps PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.P3
    (HeightOrbits.Branch1_10.P3.B:ℝ) 11745976358580478445504632320000 (11198110519606626443/281474976710656) (2799527629901656611/70368744177664) (4203619030873145/281474976710656) (20137019192144165/281474976710656) (683068736564691/281474976710656) (683563948117081/281474976710656)
  · exact HeightOrbits.Branch1_10.P3.height7
  · norm_num [PrimitiveDynamics.branch1_10]
  · simpa only [LogCertificates.Branch1_10_P3_size,HeightOrbits.Branch1_10.P3.B,
      Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,Int.cast_ofNat] using LogCertificates.Branch1_10_P3_log
  · change Real.log (3061008:ℝ)≤((4203619030873145/281474976710656):ℝ)
    simpa only [LogCertificates.Branch1_10_C_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_10_C_log.2
  · simpa only [LogCertificates.Branch1_10_D_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_10_D_log.2
  · norm_num
  · norm_num

theorem Branch1_10_S12_height : ((403438511068675/140737488355328):ℝ)≤canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.S12 ∧
    canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.S12≤((201843058422435/70368744177664):ℝ) := by
  apply from_seven_steps PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.S12
    (HeightOrbits.Branch1_10.S12.B:ℝ) 11745976358580478445504632320000 (13226585470429061157/281474976710656) (6613292735214530579/140737488355328) (4203619030873145/281474976710656) (20137019192144165/281474976710656) (403438511068675/140737488355328) (201843058422435/70368744177664)
  · exact HeightOrbits.Branch1_10.S12.height7
  · norm_num [PrimitiveDynamics.branch1_10]
  · simpa only [LogCertificates.Branch1_10_S12_size,HeightOrbits.Branch1_10.S12.B,
      Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,Int.cast_ofNat] using LogCertificates.Branch1_10_S12_log
  · change Real.log (3061008:ℝ)≤((4203619030873145/281474976710656):ℝ)
    simpa only [LogCertificates.Branch1_10_C_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_10_C_log.2
  · simpa only [LogCertificates.Branch1_10_D_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_10_D_log.2
  · norm_num
  · norm_num

theorem Branch1_10_S13_height : ((2639177818358167/281474976710656):ℝ)≤canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.S13 ∧
    canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.S13≤((2639673029910557/281474976710656):ℝ) := by
  apply from_seven_steps PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.S13
    (HeightOrbits.Branch1_10.S13.B:ℝ) 11745976358580478445504632320000 (2702937607231932951/17592186044416) (43247001715710927217/281474976710656) (4203619030873145/281474976710656) (20137019192144165/281474976710656) (2639177818358167/281474976710656) (2639673029910557/281474976710656)
  · exact HeightOrbits.Branch1_10.S13.height7
  · norm_num [PrimitiveDynamics.branch1_10]
  · simpa only [LogCertificates.Branch1_10_S13_size,HeightOrbits.Branch1_10.S13.B,
      Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,Int.cast_ofNat] using LogCertificates.Branch1_10_S13_log
  · change Real.log (3061008:ℝ)≤((4203619030873145/281474976710656):ℝ)
    simpa only [LogCertificates.Branch1_10_C_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_10_C_log.2
  · simpa only [LogCertificates.Branch1_10_D_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_10_D_log.2
  · norm_num
  · norm_num

theorem Branch1_10_S23_height : ((2204799160196033/281474976710656):ℝ)≤canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.S23 ∧
    canonicalHeight PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.S23≤((2205294371748423/281474976710656):ℝ) := by
  apply from_seven_steps PrimitiveDynamics.branch1_10 HeightPoints.Branch1_10.S23
    (HeightOrbits.Branch1_10.S23.B:ℝ) 11745976358580478445504632320000 (36130141780382523929/281474976710656) (18065070890191261965/140737488355328) (4203619030873145/281474976710656) (20137019192144165/281474976710656) (2204799160196033/281474976710656) (2205294371748423/281474976710656)
  · exact HeightOrbits.Branch1_10.S23.height7
  · norm_num [PrimitiveDynamics.branch1_10]
  · simpa only [LogCertificates.Branch1_10_S23_size,HeightOrbits.Branch1_10.S23.B,
      Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,Int.cast_ofNat] using LogCertificates.Branch1_10_S23_log
  · change Real.log (3061008:ℝ)≤((4203619030873145/281474976710656):ℝ)
    simpa only [LogCertificates.Branch1_10_C_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_10_C_log.2
  · simpa only [LogCertificates.Branch1_10_D_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch1_10_D_log.2
  · norm_num
  · norm_num

theorem Branch2_5_P1_height : ((88326205004897/140737488355328):ℝ)≤canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.P1 ∧
    canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.P1≤((177113449569131/281474976710656):ℝ) := by
  apply from_seven_steps PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.P1
    (HeightOrbits.Branch2_5.P1.B:ℝ) 32869001852808792438597120000 (90638557905355659/8796093022208) (2900433852971381089/281474976710656) (4178714307779439/281474976710656) (18482302112708831/281474976710656) (88326205004897/140737488355328) (177113449569131/281474976710656)
  · exact HeightOrbits.Branch2_5.P1.height7
  · norm_num [PrimitiveDynamics.branch2_5]
  · simpa only [LogCertificates.Branch2_5_P1_size,HeightOrbits.Branch2_5.P1.B,
      Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,Int.cast_ofNat] using LogCertificates.Branch2_5_P1_log
  · change Real.log (2801808:ℝ)≤((4178714307779439/281474976710656):ℝ)
    simpa only [LogCertificates.Branch2_5_C_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch2_5_C_log.2
  · simpa only [LogCertificates.Branch2_5_D_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch2_5_D_log.2
  · norm_num
  · norm_num

theorem Branch2_5_P2_height : ((152173520262289/70368744177664):ℝ)≤canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.P2 ∧
    canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.P2≤((609155120608493/281474976710656):ℝ) := by
  apply from_seven_steps PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.P2
    (HeightOrbits.Branch2_5.P2.B:ℝ) 32869001852808792438597120000 (9979004591280275273/281474976710656) (4989502295640137637/140737488355328) (4178714307779439/281474976710656) (18482302112708831/281474976710656) (152173520262289/70368744177664) (609155120608493/281474976710656)
  · exact HeightOrbits.Branch2_5.P2.height7
  · norm_num [PrimitiveDynamics.branch2_5]
  · simpa only [LogCertificates.Branch2_5_P2_size,HeightOrbits.Branch2_5.P2.B,
      Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,Int.cast_ofNat] using LogCertificates.Branch2_5_P2_log
  · change Real.log (2801808:ℝ)≤((4178714307779439/281474976710656):ℝ)
    simpa only [LogCertificates.Branch2_5_C_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch2_5_C_log.2
  · simpa only [LogCertificates.Branch2_5_D_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch2_5_D_log.2
  · norm_num
  · norm_num

theorem Branch2_5_P3_height : ((614722085831731/281474976710656):ℝ)≤canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.P3 ∧
    canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.P3≤((153795781347767/70368744177664):ℝ) := by
  apply from_seven_steps PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.P3
    (HeightOrbits.Branch2_5.P3.B:ℝ) 32869001852808792438597120000 (10077767421637986169/281474976710656) (5038883710818993085/140737488355328) (4178714307779439/281474976710656) (18482302112708831/281474976710656) (614722085831731/281474976710656) (153795781347767/70368744177664)
  · exact HeightOrbits.Branch2_5.P3.height7
  · norm_num [PrimitiveDynamics.branch2_5]
  · simpa only [LogCertificates.Branch2_5_P3_size,HeightOrbits.Branch2_5.P3.B,
      Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,Int.cast_ofNat] using LogCertificates.Branch2_5_P3_log
  · change Real.log (2801808:ℝ)≤((4178714307779439/281474976710656):ℝ)
    simpa only [LogCertificates.Branch2_5_C_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch2_5_C_log.2
  · simpa only [LogCertificates.Branch2_5_D_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch2_5_D_log.2
  · norm_num
  · norm_num

theorem Branch2_5_S12_height : ((406667052853497/281474976710656):ℝ)≤canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.S12 ∧
    canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.S12≤((203564046206417/140737488355328):ℝ) := by
  apply from_seven_steps PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.S12
    (HeightOrbits.Branch2_5.S12.B:ℝ) 32869001852808792438597120000 (833624220165326369/35184372088832) (6668993761322610953/281474976710656) (4178714307779439/281474976710656) (18482302112708831/281474976710656) (406667052853497/281474976710656) (203564046206417/140737488355328)
  · exact HeightOrbits.Branch2_5.S12.height7
  · norm_num [PrimitiveDynamics.branch2_5]
  · simpa only [LogCertificates.Branch2_5_S12_size,HeightOrbits.Branch2_5.S12.B,
      Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,Int.cast_ofNat] using LogCertificates.Branch2_5_S12_log
  · change Real.log (2801808:ℝ)≤((4178714307779439/281474976710656):ℝ)
    simpa only [LogCertificates.Branch2_5_C_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch2_5_C_log.2
  · simpa only [LogCertificates.Branch2_5_D_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch2_5_D_log.2
  · norm_num
  · norm_num

theorem Branch2_5_S13_height : ((601802321280363/140737488355328):ℝ)≤canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.S13 ∧
    canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.S13≤((1204065682120063/281474976710656):ℝ) := by
  apply from_seven_steps PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.S13
    (HeightOrbits.Branch2_5.S13.B:ℝ) 32869001852808792438597120000 (4931504807771462887/70368744177664) (19726019231085851549/281474976710656) (4178714307779439/281474976710656) (18482302112708831/281474976710656) (601802321280363/140737488355328) (1204065682120063/281474976710656)
  · exact HeightOrbits.Branch2_5.S13.height7
  · norm_num [PrimitiveDynamics.branch2_5]
  · simpa only [LogCertificates.Branch2_5_S13_size,HeightOrbits.Branch2_5.S13.B,
      Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,Int.cast_ofNat] using LogCertificates.Branch2_5_S13_log
  · change Real.log (2801808:ℝ)≤((4178714307779439/281474976710656):ℝ)
    simpa only [LogCertificates.Branch2_5_C_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch2_5_C_log.2
  · simpa only [LogCertificates.Branch2_5_D_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch2_5_D_log.2
  · norm_num
  · norm_num

theorem Branch2_5_S23_height : ((1001212437183885/281474976710656):ℝ)≤canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.S23 ∧
    canonicalHeight PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.S23≤((500836738371611/140737488355328):ℝ) := by
  apply from_seven_steps PrimitiveDynamics.branch2_5 HeightPoints.Branch2_5.S23
    (HeightOrbits.Branch2_5.S23.B:ℝ) 32869001852808792438597120000 (16410025338191676301/281474976710656) (8205012669095838151/140737488355328) (4178714307779439/281474976710656) (18482302112708831/281474976710656) (1001212437183885/281474976710656) (500836738371611/140737488355328)
  · exact HeightOrbits.Branch2_5.S23.height7
  · norm_num [PrimitiveDynamics.branch2_5]
  · simpa only [LogCertificates.Branch2_5_S23_size,HeightOrbits.Branch2_5.S23.B,
      Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,Int.cast_ofNat] using LogCertificates.Branch2_5_S23_log
  · change Real.log (2801808:ℝ)≤((4178714307779439/281474976710656):ℝ)
    simpa only [LogCertificates.Branch2_5_C_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch2_5_C_log.2
  · simpa only [LogCertificates.Branch2_5_D_size,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] using LogCertificates.Branch2_5_D_log.2
  · norm_num
  · norm_num

end LcmSix.HeightIntervals
