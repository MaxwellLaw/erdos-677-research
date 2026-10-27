/-
Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
-/
import LcmSix.GramBounds

/-!
# Four exact rational Gram lower-bound certificates

Generated from height_intervals.json by scripts/export_gram_certificates.py.
All entries, radii, LDL identities and positivity are kernel checked. Each
height conclusion explicitly assumes six closed height intervals. No actual
elliptic point or orbit-height interval is asserted by these conditional
bridges; the separate actual-point development must discharge those premises.
-/

namespace LcmSix.GramBounds

noncomputable def branch1_2_midpoint : Sym3 where
  d1 := (276293687844657/562949953421312 : ℝ)
  d2 := (999317190179575/562949953421312 : ℝ)
  d3 := (40924485642159/35184372088832 : ℝ)
  e12 := (-173135376734955/281474976710656 : ℝ)
  e13 := (77077387139411/562949953421312 : ℝ)
  e23 := (-293926338224833/562949953421312 : ℝ)

noncomputable def branch1_2_radius : Sym3 where
  d1 := (277135716141/562949953421312 : ℝ)
  d2 := (277135716141/562949953421312 : ℝ)
  d3 := (138567858071/281474976710656 : ℝ)
  e12 := (103925893553/140737488355328 : ℝ)
  e13 := (415703574213/562949953421312 : ℝ)
  e23 := (415703574213/562949953421312 : ℝ)

noncomputable def branch1_2_rho : ℝ := (138567858071/70368744177664 : ℝ)

noncomputable def branch1_2_squares : SquareCertificate where
  d1 := (6738891136146897/14073748835532800 : ℝ)
  d2 := (30760807943239609503455981300753/31613820426709899746651353907200 : ℝ)
  d3 := (321060368831412546901861169587023775553133780287/324689913728412419135457456936521748907347148800 : ℝ)
  l21 := (-2885589612249250/2246297045382299 : ℝ)
  l31 := (1926934678485275/6738891136146897 : ℝ)
  l32 := (-10945803936142058563811755982925/30760807943239609503455981300753 : ℝ)

theorem branch1_2_squares_valid :
    branch1_2_squares.Valid branch1_2_midpoint ((1/100 : ℝ)+branch1_2_rho) := by
  norm_num [SquareCertificate.Valid,branch1_2_squares,branch1_2_midpoint,branch1_2_rho]

theorem branch1_2_row_radii :
    branch1_2_radius.d1+branch1_2_radius.e12+branch1_2_radius.e13 ≤ branch1_2_rho ∧
    branch1_2_radius.d2+branch1_2_radius.e12+branch1_2_radius.e23 ≤ branch1_2_rho ∧
    branch1_2_radius.d3+branch1_2_radius.e13+branch1_2_radius.e23 ≤ branch1_2_rho := by
  norm_num [branch1_2_radius,branch1_2_rho]

/-- Convert six explicit height intervals into the symmetric pairing intervals. -/
theorem branch1_2_height_entries
    (h1 h2 h3 h12 h13 h23 : ℝ)
    (h_h1 : (69004138032129/140737488355328 : ℝ) ≤ h1 ∧ h1 ≤ (138285411780399/281474976710656 : ℝ))
    (h_h2 : (499520027231717/281474976710656 : ℝ) ≤ h2 ∧ h2 ≤ (249898581473929/140737488355328 : ℝ))
    (h_h3 : (327257317279201/281474976710656 : ℝ) ≤ h3 ∧ h3 ≤ (327534452995343/281474976710656 : ℝ))
    (h_h12 : (291396117684135/281474976710656 : ℝ) ≤ h12 ∧ h12 ≤ (291673253400277/281474976710656 : ℝ))
    (h_h13 : (542481548340941/281474976710656 : ℝ) ≤ h13 ∧ h13 ≤ (271379342028541/140737488355328 : ℝ))
    (h_h23 : (133247393536039/70368744177664 : ℝ) ≤ h23 ∧ h23 ≤ (266633354930149/140737488355328 : ℝ))
    : EntryBounds (fromHeights h1 h2 h3 h12 h13 h23) branch1_2_midpoint branch1_2_radius := by
  simp only [EntryBounds,fromHeights,branch1_2_midpoint,branch1_2_radius,abs_le]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    linarith only [h_h1.1, h_h1.2, h_h2.1, h_h2.2, h_h3.1, h_h3.2, h_h12.1, h_h12.2, h_h13.1, h_h13.2, h_h23.1, h_h23.2]

/-- A conditional lower bound for all real coefficient triples. -/
theorem branch1_2_height_lower
    (h1 h2 h3 h12 h13 h23 : ℝ)
    (h_h1 : (69004138032129/140737488355328 : ℝ) ≤ h1 ∧ h1 ≤ (138285411780399/281474976710656 : ℝ))
    (h_h2 : (499520027231717/281474976710656 : ℝ) ≤ h2 ∧ h2 ≤ (249898581473929/140737488355328 : ℝ))
    (h_h3 : (327257317279201/281474976710656 : ℝ) ≤ h3 ∧ h3 ≤ (327534452995343/281474976710656 : ℝ))
    (h_h12 : (291396117684135/281474976710656 : ℝ) ≤ h12 ∧ h12 ≤ (291673253400277/281474976710656 : ℝ))
    (h_h13 : (542481548340941/281474976710656 : ℝ) ≤ h13 ∧ h13 ≤ (271379342028541/140737488355328 : ℝ))
    (h_h23 : (133247393536039/70368744177664 : ℝ) ≤ h23 ∧ h23 ≤ (266633354930149/140737488355328 : ℝ))
    (x y z : ℝ) :
    (x^2+y^2+z^2)/100 ≤
      h1*x^2+h2*y^2+h3*z^2+(h12-h1-h2)*x*y+
        (h13-h1-h3)*x*z+(h23-h2-h3)*y*z := by
  obtain ⟨hr1,hr2,hr3⟩ := branch1_2_row_radii
  have h := certified_lower (fromHeights h1 h2 h3 h12 h13 h23)
    branch1_2_midpoint branch1_2_radius branch1_2_rho (1/100) branch1_2_squares
    branch1_2_squares_valid
    (branch1_2_height_entries h1 h2 h3 h12 h13 h23 h_h1 h_h2 h_h3 h_h12 h_h13 h_h23)
    hr1 hr2 hr3 x y z
  rw [quad_fromHeights] at h
  have he : (1/100 : ℝ)*(x^2+y^2+z^2)=(x^2+y^2+z^2)/100 := by ring
  rw [he] at h
  exact h

/-- The same conditional bound for arbitrary integer coefficient triples. -/
theorem branch1_2_integer_lower
    (h1 h2 h3 h12 h13 h23 : ℝ)
    (h_h1 : (69004138032129/140737488355328 : ℝ) ≤ h1 ∧ h1 ≤ (138285411780399/281474976710656 : ℝ))
    (h_h2 : (499520027231717/281474976710656 : ℝ) ≤ h2 ∧ h2 ≤ (249898581473929/140737488355328 : ℝ))
    (h_h3 : (327257317279201/281474976710656 : ℝ) ≤ h3 ∧ h3 ≤ (327534452995343/281474976710656 : ℝ))
    (h_h12 : (291396117684135/281474976710656 : ℝ) ≤ h12 ∧ h12 ≤ (291673253400277/281474976710656 : ℝ))
    (h_h13 : (542481548340941/281474976710656 : ℝ) ≤ h13 ∧ h13 ≤ (271379342028541/140737488355328 : ℝ))
    (h_h23 : (133247393536039/70368744177664 : ℝ) ≤ h23 ∧ h23 ≤ (266633354930149/140737488355328 : ℝ))
    (m : Fin 3 → ℤ) :
    ((m 0 : ℝ)^2+(m 1 : ℝ)^2+(m 2 : ℝ)^2)/100 ≤
      h1*(m 0 : ℝ)^2+h2*(m 1 : ℝ)^2+h3*(m 2 : ℝ)^2+
        (h12-h1-h2)*(m 0 : ℝ)*(m 1 : ℝ)+
        (h13-h1-h3)*(m 0 : ℝ)*(m 2 : ℝ)+
        (h23-h2-h3)*(m 1 : ℝ)*(m 2 : ℝ) :=
  branch1_2_height_lower h1 h2 h3 h12 h13 h23 h_h1 h_h2 h_h3 h_h12 h_h13 h_h23 (m 0) (m 1) (m 2)

noncomputable def branch1_5_midpoint : Sym3 where
  d1 := (364142943285345/562949953421312 : ℝ)
  d2 := (674318790805459/281474976710656 : ℝ)
  d3 := (453255262702209/140737488355328 : ℝ)
  e12 := (174979970791469/281474976710656 : ℝ)
  e13 := (159031795902151/140737488355328 : ℝ)
  e23 := (497297053003305/281474976710656 : ℝ)

noncomputable def branch1_5_radius : Sym3 where
  d1 := (403392000807/562949953421312 : ℝ)
  d2 := (50424000101/70368744177664 : ℝ)
  d3 := (50424000101/70368744177664 : ℝ)
  e12 := (151272000303/140737488355328 : ℝ)
  e13 := (151272000303/140737488355328 : ℝ)
  e23 := (151272000303/140737488355328 : ℝ)

noncomputable def branch1_5_rho : ℝ := (50424000101/17592186044416 : ℝ)

noncomputable def branch1_5_squares : SquareCertificate where
  d1 := (8922496893697497/14073748835532800 : ℝ)
  d2 := (111334867090313634463426864466017/62786490133860086795564010700800 : ℝ)
  d3 := (743442169616658150666138342695782993510004100937/783449478033250284999994394164211742113844428800 : ℝ)
  l21 := (8748998539573450/8922496893697497 : ℝ)
  l31 := (15903179590215100/8922496893697497 : ℝ)
  l32 := (41359837761989606129376406142125/111334867090313634463426864466017 : ℝ)

theorem branch1_5_squares_valid :
    branch1_5_squares.Valid branch1_5_midpoint ((1/100 : ℝ)+branch1_5_rho) := by
  norm_num [SquareCertificate.Valid,branch1_5_squares,branch1_5_midpoint,branch1_5_rho]

theorem branch1_5_row_radii :
    branch1_5_radius.d1+branch1_5_radius.e12+branch1_5_radius.e13 ≤ branch1_5_rho ∧
    branch1_5_radius.d2+branch1_5_radius.e12+branch1_5_radius.e23 ≤ branch1_5_rho ∧
    branch1_5_radius.d3+branch1_5_radius.e13+branch1_5_radius.e23 ≤ branch1_5_rho := by
  norm_num [branch1_5_radius,branch1_5_rho]

/-- Convert six explicit height intervals into the symmetric pairing intervals. -/
theorem branch1_5_height_entries
    (h1 h2 h3 h12 h13 h23 : ℝ)
    (h_h1 : (181869775642269/281474976710656 : ℝ) ≤ h1 ∧ h1 ≤ (45568291910769/70368744177664 : ℝ))
    (h_h2 : (674117094805055/281474976710656 : ℝ) ≤ h2 ∧ h2 ≤ (674520486805863/281474976710656 : ℝ))
    (h_h3 : (453154414702007/140737488355328 : ℝ) ≤ h3 ∧ h3 ≤ (453356110702411/140737488355328 : ℝ))
    (h_h12 : (603074254015333/140737488355328 : ℝ) ≤ h12 ∧ h12 ≤ (603275950015737/140737488355328 : ℝ))
    (h_h13 : (1724507484655291/281474976710656 : ℝ) ≤ h13 ∧ h13 ≤ (1724910876656099/281474976710656 : ℝ))
    (h_h23 : (2575221726216083/281474976710656 : ℝ) ≤ h23 ∧ h23 ≤ (1287812559108445/140737488355328 : ℝ))
    : EntryBounds (fromHeights h1 h2 h3 h12 h13 h23) branch1_5_midpoint branch1_5_radius := by
  simp only [EntryBounds,fromHeights,branch1_5_midpoint,branch1_5_radius,abs_le]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    linarith only [h_h1.1, h_h1.2, h_h2.1, h_h2.2, h_h3.1, h_h3.2, h_h12.1, h_h12.2, h_h13.1, h_h13.2, h_h23.1, h_h23.2]

/-- A conditional lower bound for all real coefficient triples. -/
theorem branch1_5_height_lower
    (h1 h2 h3 h12 h13 h23 : ℝ)
    (h_h1 : (181869775642269/281474976710656 : ℝ) ≤ h1 ∧ h1 ≤ (45568291910769/70368744177664 : ℝ))
    (h_h2 : (674117094805055/281474976710656 : ℝ) ≤ h2 ∧ h2 ≤ (674520486805863/281474976710656 : ℝ))
    (h_h3 : (453154414702007/140737488355328 : ℝ) ≤ h3 ∧ h3 ≤ (453356110702411/140737488355328 : ℝ))
    (h_h12 : (603074254015333/140737488355328 : ℝ) ≤ h12 ∧ h12 ≤ (603275950015737/140737488355328 : ℝ))
    (h_h13 : (1724507484655291/281474976710656 : ℝ) ≤ h13 ∧ h13 ≤ (1724910876656099/281474976710656 : ℝ))
    (h_h23 : (2575221726216083/281474976710656 : ℝ) ≤ h23 ∧ h23 ≤ (1287812559108445/140737488355328 : ℝ))
    (x y z : ℝ) :
    (x^2+y^2+z^2)/100 ≤
      h1*x^2+h2*y^2+h3*z^2+(h12-h1-h2)*x*y+
        (h13-h1-h3)*x*z+(h23-h2-h3)*y*z := by
  obtain ⟨hr1,hr2,hr3⟩ := branch1_5_row_radii
  have h := certified_lower (fromHeights h1 h2 h3 h12 h13 h23)
    branch1_5_midpoint branch1_5_radius branch1_5_rho (1/100) branch1_5_squares
    branch1_5_squares_valid
    (branch1_5_height_entries h1 h2 h3 h12 h13 h23 h_h1 h_h2 h_h3 h_h12 h_h13 h_h23)
    hr1 hr2 hr3 x y z
  rw [quad_fromHeights] at h
  have he : (1/100 : ℝ)*(x^2+y^2+z^2)=(x^2+y^2+z^2)/100 := by ring
  rw [he] at h
  exact h

/-- The same conditional bound for arbitrary integer coefficient triples. -/
theorem branch1_5_integer_lower
    (h1 h2 h3 h12 h13 h23 : ℝ)
    (h_h1 : (181869775642269/281474976710656 : ℝ) ≤ h1 ∧ h1 ≤ (45568291910769/70368744177664 : ℝ))
    (h_h2 : (674117094805055/281474976710656 : ℝ) ≤ h2 ∧ h2 ≤ (674520486805863/281474976710656 : ℝ))
    (h_h3 : (453154414702007/140737488355328 : ℝ) ≤ h3 ∧ h3 ≤ (453356110702411/140737488355328 : ℝ))
    (h_h12 : (603074254015333/140737488355328 : ℝ) ≤ h12 ∧ h12 ≤ (603275950015737/140737488355328 : ℝ))
    (h_h13 : (1724507484655291/281474976710656 : ℝ) ≤ h13 ∧ h13 ≤ (1724910876656099/281474976710656 : ℝ))
    (h_h23 : (2575221726216083/281474976710656 : ℝ) ≤ h23 ∧ h23 ≤ (1287812559108445/140737488355328 : ℝ))
    (m : Fin 3 → ℤ) :
    ((m 0 : ℝ)^2+(m 1 : ℝ)^2+(m 2 : ℝ)^2)/100 ≤
      h1*(m 0 : ℝ)^2+h2*(m 1 : ℝ)^2+h3*(m 2 : ℝ)^2+
        (h12-h1-h2)*(m 0 : ℝ)*(m 1 : ℝ)+
        (h13-h1-h3)*(m 0 : ℝ)*(m 2 : ℝ)+
        (h23-h2-h3)*(m 1 : ℝ)*(m 2 : ℝ) :=
  branch1_5_height_lower h1 h2 h3 h12 h13 h23 h_h1 h_h2 h_h3 h_h12 h_h13 h_h23 (m 0) (m 1) (m 2)

noncomputable def branch1_10_midpoint : Sym3 where
  d1 := (1391019805661403/281474976710656 : ℝ)
  d2 := (786173810348579/281474976710656 : ℝ)
  d3 := (341658171170443/140737488355328 : ℝ)
  e12 := (-1370068988096437/562949953421312 : ℝ)
  e13 := (565089276132073/562949953421312 : ℝ)
  e23 := (735556613282763/562949953421312 : ℝ)

noncomputable def branch1_10_radius : Sym3 where
  d1 := (247605776195/281474976710656 : ℝ)
  d2 := (247605776195/281474976710656 : ℝ)
  d3 := (247605776195/281474976710656 : ℝ)
  e12 := (742817328585/562949953421312 : ℝ)
  e13 := (742817328585/562949953421312 : ℝ)
  e23 := (742817328585/562949953421312 : ℝ)

noncomputable def branch1_10_rho : ℝ := (247605776195/70368744177664 : ℝ)

noncomputable def branch1_10_squares : SquareCertificate where
  d1 := (34680365819737911/7036874417766400 : ℝ)
  d2 := (1540102410268413764149569636153659/976165516142775887700680087961600 : ℝ)
  d3 := (1634008785471661548093388040131577071108667590649/10837507251558173407344490643053911467189967257600 : ℝ)
  l21 := (-34251724702410925/69360731639475822 : ℝ)
  l31 := (2018175986185975/9908675948496546 : ℝ)
  l32 := (1759350679447696359641145148842775/1540102410268413764149569636153659 : ℝ)

theorem branch1_10_squares_valid :
    branch1_10_squares.Valid branch1_10_midpoint ((1/100 : ℝ)+branch1_10_rho) := by
  norm_num [SquareCertificate.Valid,branch1_10_squares,branch1_10_midpoint,branch1_10_rho]

theorem branch1_10_row_radii :
    branch1_10_radius.d1+branch1_10_radius.e12+branch1_10_radius.e13 ≤ branch1_10_rho ∧
    branch1_10_radius.d2+branch1_10_radius.e12+branch1_10_radius.e23 ≤ branch1_10_rho ∧
    branch1_10_radius.d3+branch1_10_radius.e13+branch1_10_radius.e23 ≤ branch1_10_rho := by
  norm_num [branch1_10_radius,branch1_10_rho]

/-- Convert six explicit height intervals into the symmetric pairing intervals. -/
theorem branch1_10_height_entries
    (h1 h2 h3 h12 h13 h23 : ℝ)
    (h_h1 : (173846524985651/35184372088832 : ℝ) ≤ h1 ∧ h1 ≤ (695633705718799/140737488355328 : ℝ))
    (h_h2 : (24560193892887/8796093022208 : ℝ) ≤ h2 ∧ h2 ≤ (393210708062387/140737488355328 : ℝ))
    (h_h3 : (683068736564691/281474976710656 : ℝ) ≤ h3 ∧ h3 ≤ (683563948117081/281474976710656 : ℝ))
    (h_h12 : (403438511068675/140737488355328 : ℝ) ≤ h12 ∧ h12 ≤ (201843058422435/70368744177664 : ℝ))
    (h_h13 : (2639177818358167/281474976710656 : ℝ) ≤ h13 ∧ h13 ≤ (2639673029910557/281474976710656 : ℝ))
    (h_h23 : (2204799160196033/281474976710656 : ℝ) ≤ h23 ∧ h23 ≤ (2205294371748423/281474976710656 : ℝ))
    : EntryBounds (fromHeights h1 h2 h3 h12 h13 h23) branch1_10_midpoint branch1_10_radius := by
  simp only [EntryBounds,fromHeights,branch1_10_midpoint,branch1_10_radius,abs_le]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    linarith only [h_h1.1, h_h1.2, h_h2.1, h_h2.2, h_h3.1, h_h3.2, h_h12.1, h_h12.2, h_h13.1, h_h13.2, h_h23.1, h_h23.2]

/-- A conditional lower bound for all real coefficient triples. -/
theorem branch1_10_height_lower
    (h1 h2 h3 h12 h13 h23 : ℝ)
    (h_h1 : (173846524985651/35184372088832 : ℝ) ≤ h1 ∧ h1 ≤ (695633705718799/140737488355328 : ℝ))
    (h_h2 : (24560193892887/8796093022208 : ℝ) ≤ h2 ∧ h2 ≤ (393210708062387/140737488355328 : ℝ))
    (h_h3 : (683068736564691/281474976710656 : ℝ) ≤ h3 ∧ h3 ≤ (683563948117081/281474976710656 : ℝ))
    (h_h12 : (403438511068675/140737488355328 : ℝ) ≤ h12 ∧ h12 ≤ (201843058422435/70368744177664 : ℝ))
    (h_h13 : (2639177818358167/281474976710656 : ℝ) ≤ h13 ∧ h13 ≤ (2639673029910557/281474976710656 : ℝ))
    (h_h23 : (2204799160196033/281474976710656 : ℝ) ≤ h23 ∧ h23 ≤ (2205294371748423/281474976710656 : ℝ))
    (x y z : ℝ) :
    (x^2+y^2+z^2)/100 ≤
      h1*x^2+h2*y^2+h3*z^2+(h12-h1-h2)*x*y+
        (h13-h1-h3)*x*z+(h23-h2-h3)*y*z := by
  obtain ⟨hr1,hr2,hr3⟩ := branch1_10_row_radii
  have h := certified_lower (fromHeights h1 h2 h3 h12 h13 h23)
    branch1_10_midpoint branch1_10_radius branch1_10_rho (1/100) branch1_10_squares
    branch1_10_squares_valid
    (branch1_10_height_entries h1 h2 h3 h12 h13 h23 h_h1 h_h2 h_h3 h_h12 h_h13 h_h23)
    hr1 hr2 hr3 x y z
  rw [quad_fromHeights] at h
  have he : (1/100 : ℝ)*(x^2+y^2+z^2)=(x^2+y^2+z^2)/100 := by ring
  rw [he] at h
  exact h

/-- The same conditional bound for arbitrary integer coefficient triples. -/
theorem branch1_10_integer_lower
    (h1 h2 h3 h12 h13 h23 : ℝ)
    (h_h1 : (173846524985651/35184372088832 : ℝ) ≤ h1 ∧ h1 ≤ (695633705718799/140737488355328 : ℝ))
    (h_h2 : (24560193892887/8796093022208 : ℝ) ≤ h2 ∧ h2 ≤ (393210708062387/140737488355328 : ℝ))
    (h_h3 : (683068736564691/281474976710656 : ℝ) ≤ h3 ∧ h3 ≤ (683563948117081/281474976710656 : ℝ))
    (h_h12 : (403438511068675/140737488355328 : ℝ) ≤ h12 ∧ h12 ≤ (201843058422435/70368744177664 : ℝ))
    (h_h13 : (2639177818358167/281474976710656 : ℝ) ≤ h13 ∧ h13 ≤ (2639673029910557/281474976710656 : ℝ))
    (h_h23 : (2204799160196033/281474976710656 : ℝ) ≤ h23 ∧ h23 ≤ (2205294371748423/281474976710656 : ℝ))
    (m : Fin 3 → ℤ) :
    ((m 0 : ℝ)^2+(m 1 : ℝ)^2+(m 2 : ℝ)^2)/100 ≤
      h1*(m 0 : ℝ)^2+h2*(m 1 : ℝ)^2+h3*(m 2 : ℝ)^2+
        (h12-h1-h2)*(m 0 : ℝ)*(m 1 : ℝ)+
        (h13-h1-h3)*(m 0 : ℝ)*(m 2 : ℝ)+
        (h23-h2-h3)*(m 1 : ℝ)*(m 2 : ℝ) :=
  branch1_10_height_lower h1 h2 h3 h12 h13 h23 h_h1 h_h2 h_h3 h_h12 h_h13 h_h23 (m 0) (m 1) (m 2)

noncomputable def branch2_5_midpoint : Sym3 where
  d1 := (353765859578925/562949953421312 : ℝ)
  d2 := (1217849201657649/562949953421312 : ℝ)
  d3 := (1229905211222799/562949953421312 : ℝ)
  e12 := (-189454978992561/281474976710656 : ℝ)
  e13 := (102999906734883/140737488355328 : ℝ)
  e23 := (-111217124738335/281474976710656 : ℝ)

noncomputable def branch2_5_radius : Sym3 where
  d1 := (461039559337/562949953421312 : ℝ)
  d2 := (461039559337/562949953421312 : ℝ)
  d3 := (461039559337/562949953421312 : ℝ)
  e12 := (345779669503/281474976710656 : ℝ)
  e13 := (345779669503/281474976710656 : ℝ)
  e23 := (345779669503/281474976710656 : ℝ)

noncomputable def branch2_5_rho : ℝ := (1844158237349/562949953421312 : ℝ)

noncomputable def branch2_5_squares : SquareCertificate where
  d1 := (1082163130648009/1759218604441600 : ℝ)
  d2 := (43057946225907888227482346950471/30460184199627891949657548390400 : ℝ)
  d3 := (358844057729089239463543780487837755719422722131/302993360278652531254001809112429816703247974400 : ℝ)
  l21 := (-4736374474814025/4328652522592036 : ℝ)
  l31 := (2574997668372075/2164326261296018 : ℝ)
  l32 := (12356799269515578045508884202250/43057946225907888227482346950471 : ℝ)

theorem branch2_5_squares_valid :
    branch2_5_squares.Valid branch2_5_midpoint ((1/100 : ℝ)+branch2_5_rho) := by
  norm_num [SquareCertificate.Valid,branch2_5_squares,branch2_5_midpoint,branch2_5_rho]

theorem branch2_5_row_radii :
    branch2_5_radius.d1+branch2_5_radius.e12+branch2_5_radius.e13 ≤ branch2_5_rho ∧
    branch2_5_radius.d2+branch2_5_radius.e12+branch2_5_radius.e23 ≤ branch2_5_rho ∧
    branch2_5_radius.d3+branch2_5_radius.e13+branch2_5_radius.e23 ≤ branch2_5_rho := by
  norm_num [branch2_5_radius,branch2_5_rho]

/-- Convert six explicit height intervals into the symmetric pairing intervals. -/
theorem branch2_5_height_entries
    (h1 h2 h3 h12 h13 h23 : ℝ)
    (h_h1 : (88326205004897/140737488355328 : ℝ) ≤ h1 ∧ h1 ≤ (177113449569131/281474976710656 : ℝ))
    (h_h2 : (152173520262289/70368744177664 : ℝ) ≤ h2 ∧ h2 ≤ (609155120608493/281474976710656 : ℝ))
    (h_h3 : (614722085831731/281474976710656 : ℝ) ≤ h3 ∧ h3 ≤ (153795781347767/70368744177664 : ℝ))
    (h_h12 : (406667052853497/281474976710656 : ℝ) ≤ h12 ∧ h12 ≤ (203564046206417/140737488355328 : ℝ))
    (h_h13 : (601802321280363/140737488355328 : ℝ) ≤ h13 ∧ h13 ≤ (1204065682120063/281474976710656 : ℝ))
    (h_h23 : (1001212437183885/281474976710656 : ℝ) ≤ h23 ∧ h23 ≤ (500836738371611/140737488355328 : ℝ))
    : EntryBounds (fromHeights h1 h2 h3 h12 h13 h23) branch2_5_midpoint branch2_5_radius := by
  simp only [EntryBounds,fromHeights,branch2_5_midpoint,branch2_5_radius,abs_le]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    linarith only [h_h1.1, h_h1.2, h_h2.1, h_h2.2, h_h3.1, h_h3.2, h_h12.1, h_h12.2, h_h13.1, h_h13.2, h_h23.1, h_h23.2]

/-- A conditional lower bound for all real coefficient triples. -/
theorem branch2_5_height_lower
    (h1 h2 h3 h12 h13 h23 : ℝ)
    (h_h1 : (88326205004897/140737488355328 : ℝ) ≤ h1 ∧ h1 ≤ (177113449569131/281474976710656 : ℝ))
    (h_h2 : (152173520262289/70368744177664 : ℝ) ≤ h2 ∧ h2 ≤ (609155120608493/281474976710656 : ℝ))
    (h_h3 : (614722085831731/281474976710656 : ℝ) ≤ h3 ∧ h3 ≤ (153795781347767/70368744177664 : ℝ))
    (h_h12 : (406667052853497/281474976710656 : ℝ) ≤ h12 ∧ h12 ≤ (203564046206417/140737488355328 : ℝ))
    (h_h13 : (601802321280363/140737488355328 : ℝ) ≤ h13 ∧ h13 ≤ (1204065682120063/281474976710656 : ℝ))
    (h_h23 : (1001212437183885/281474976710656 : ℝ) ≤ h23 ∧ h23 ≤ (500836738371611/140737488355328 : ℝ))
    (x y z : ℝ) :
    (x^2+y^2+z^2)/100 ≤
      h1*x^2+h2*y^2+h3*z^2+(h12-h1-h2)*x*y+
        (h13-h1-h3)*x*z+(h23-h2-h3)*y*z := by
  obtain ⟨hr1,hr2,hr3⟩ := branch2_5_row_radii
  have h := certified_lower (fromHeights h1 h2 h3 h12 h13 h23)
    branch2_5_midpoint branch2_5_radius branch2_5_rho (1/100) branch2_5_squares
    branch2_5_squares_valid
    (branch2_5_height_entries h1 h2 h3 h12 h13 h23 h_h1 h_h2 h_h3 h_h12 h_h13 h_h23)
    hr1 hr2 hr3 x y z
  rw [quad_fromHeights] at h
  have he : (1/100 : ℝ)*(x^2+y^2+z^2)=(x^2+y^2+z^2)/100 := by ring
  rw [he] at h
  exact h

/-- The same conditional bound for arbitrary integer coefficient triples. -/
theorem branch2_5_integer_lower
    (h1 h2 h3 h12 h13 h23 : ℝ)
    (h_h1 : (88326205004897/140737488355328 : ℝ) ≤ h1 ∧ h1 ≤ (177113449569131/281474976710656 : ℝ))
    (h_h2 : (152173520262289/70368744177664 : ℝ) ≤ h2 ∧ h2 ≤ (609155120608493/281474976710656 : ℝ))
    (h_h3 : (614722085831731/281474976710656 : ℝ) ≤ h3 ∧ h3 ≤ (153795781347767/70368744177664 : ℝ))
    (h_h12 : (406667052853497/281474976710656 : ℝ) ≤ h12 ∧ h12 ≤ (203564046206417/140737488355328 : ℝ))
    (h_h13 : (601802321280363/140737488355328 : ℝ) ≤ h13 ∧ h13 ≤ (1204065682120063/281474976710656 : ℝ))
    (h_h23 : (1001212437183885/281474976710656 : ℝ) ≤ h23 ∧ h23 ≤ (500836738371611/140737488355328 : ℝ))
    (m : Fin 3 → ℤ) :
    ((m 0 : ℝ)^2+(m 1 : ℝ)^2+(m 2 : ℝ)^2)/100 ≤
      h1*(m 0 : ℝ)^2+h2*(m 1 : ℝ)^2+h3*(m 2 : ℝ)^2+
        (h12-h1-h2)*(m 0 : ℝ)*(m 1 : ℝ)+
        (h13-h1-h3)*(m 0 : ℝ)*(m 2 : ℝ)+
        (h23-h2-h3)*(m 1 : ℝ)*(m 2 : ℝ) :=
  branch2_5_height_lower h1 h2 h3 h12 h13 h23 h_h1 h_h2 h_h3 h_h12 h_h13 h_h23 (m 0) (m 1) (m 2)

end LcmSix.GramBounds
