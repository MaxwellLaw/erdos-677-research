/-
Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
-/
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
Exact integer algebra certificates for four homogeneous duplication pairs.
The coefficient witnesses were discovered by external symbolic arithmetic;
all identities and divisibility conclusions below are proved by Lean.
This file does not formalize canonical heights, elliptic logarithms, or an
integral-point completeness theorem. It proves no k=6 noncollision endpoint.
-/

namespace HeightCertificates

def homogeneousQuartic (c0 c1 c2 c3 c4 p q : ℤ) : ℤ :=
  c0 * p^4 + c1 * p^3*q + c2 * p^2*q^2 + c3 * p*q^3 + c4 * q^4

def homogeneousCubic (c0 c1 c2 c3 p q : ℤ) : ℤ :=
  c0 * p^3 + c1 * p^2*q + c2 * p*q^2 + c3 * q^3

/-- Homogeneous numerator, for the specified a1=a3=0 models. -/
def F (a2 a4 a6 p q : ℤ) : ℤ :=
  homogeneousQuartic 1 0 (-2*a4) (-8*a6) (a4^2-4*a2*a6) p q

/-- Homogeneous denominator, for the specified a1=a3=0 models. -/
def G (a2 a4 a6 p q : ℤ) : ℤ :=
  homogeneousQuartic 0 4 (4*a2) (4*a4) (4*a6) p q

def FCoefficients (a2 a4 a6 : ℤ) : List ℤ :=
  [1, 0, -2*a4, -8*a6, a4^2-4*a2*a6]

def GCoefficients (a2 a4 a6 : ℤ) : List ℤ :=
  [0, 4, 4*a2, 4*a4, 4*a6]

def coefficientAbsSum (xs : List ℤ) : ℤ := (xs.map abs).sum

/-- Two fixed polynomial Bezout identities bound any common integer divisor. -/
theorem common_divisor_of_bezout7
    {p q d f g R u v u' v' : ℤ}
    (hcop : IsCoprime p q) (hf : d ∣ f) (hg : d ∣ g)
    (hp : u*f + v*g = R*p^7)
    (hq : u'*f + v'*g = R*q^7) : d ∣ R := by
  have hdp : d ∣ R*p^7 := by
    rw [← hp]
    exact dvd_add (dvd_mul_of_dvd_right hf u) (dvd_mul_of_dvd_right hg v)
  have hdq : d ∣ R*q^7 := by
    rw [← hq]
    exact dvd_add (dvd_mul_of_dvd_right hf u') (dvd_mul_of_dvd_right hg v')
  obtain ⟨r, s, hrs⟩ := hcop.pow (m := 7) (n := 7)
  have hlin : d ∣ r*(R*p^7) + s*(R*q^7) :=
    dvd_add (dvd_mul_of_dvd_right hdp r) (dvd_mul_of_dvd_right hdq s)
  have heq : r*(R*p^7) + s*(R*q^7) = R := by
    calc
      _ = R*(r*p^7+s*q^7) := by ring
      _ = R := by rw [hrs, mul_one]
  rwa [heq] at hlin

namespace Branch1_2

def numerator (p q : ℤ) : ℤ := F (-1) (-65) 261 p q
def denominator (p q : ℤ) : ℤ := G (-1) (-65) 261 p q

def Up (p q : ℤ) : ℤ := homogeneousCubic 47362584674304 (-196019996774400) (-3221155890044928) 17457739501105152 p q
def Vp (p q : ℤ) : ℤ := homogeneousCubic 49004999193600 (-684990030210048) 29229819137252352 (-88108074167933952) p q
def Uq (p q : ℤ) : ℤ := homogeneousCubic 0 330338304 (-220225536) (-28739432448) p q
def Vq (p q : ℤ) : ℤ := homogeneousCubic (-82584576) (-27528192) (-8946662400) 190412504064 p q

theorem bezout_p7 (p q : ℤ) :
    Up p q * numerator p q + Vp p q * denominator p q = 47362584674304 * p^7 := by
  unfold Up Vp numerator denominator F G homogeneousCubic homogeneousQuartic
  ring

theorem bezout_q7 (p q : ℤ) :
    Uq p q * numerator p q + Vq p q * denominator p q = 47362584674304 * q^7 := by
  unfold Uq Vq numerator denominator F G homogeneousCubic homogeneousQuartic
  ring

/-- All integer common divisors, with primitive integer coordinates. -/
theorem common_divisor_bound {p q d : ℤ} (hcop : IsCoprime p q)
    (hf : d ∣ numerator p q) (hg : d ∣ denominator p q) :
    d ∣ 47362584674304 :=
  common_divisor_of_bezout7 hcop hf hg (bezout_p7 p q) (bezout_q7 p q)

/-- Exact maximum of the numerator/denominator absolute coefficient sums. -/
theorem coefficient_C :
    max (coefficientAbsSum (FCoefficients (-1) (-65) 261))
      (coefficientAbsSum (GCoefficients (-1) (-65) 261)) = 7488 := by
  norm_num [coefficientAbsSum, FCoefficients, GCoefficients]

/-- Exact maximum of the two eight-coefficient witness absolute sums. -/
theorem coefficient_D :
    max (coefficientAbsSum [47362584674304, -196019996774400, -3221155890044928, 17457739501105152, 49004999193600, -684990030210048, 29229819137252352, -88108074167933952])
      (coefficientAbsSum [0, 330338304, -220225536, -28739432448, -82584576, -27528192, -8946662400, 190412504064]) = 138994166307188736 := by
  norm_num [coefficientAbsSum]

end Branch1_2

namespace Branch1_5

def numerator (p q : ℤ) : ℤ := F (-1) (-408) 6912 p q
def denominator (p q : ℤ) : ℤ := G (-1) (-408) 6912 p q

def Up (p q : ℤ) : ℤ := homogeneousCubic 239541243494400000000 (-482321205842411520000) (-81856728512405176320000) 1555928294470944030720000 p q
def Vp (p q : ℤ) : ℤ := homogeneousCubic 120580301460602880000 (-28281651243295703040000) 3041744714193331814400000 (-10923913234098086215680000) p q
def Uq (p q : ℤ) : ℤ := homogeneousCubic 0 742901760000 (-495267840000) (-404386191360000) p q
def Vq (p q : ℤ) : ℤ := homogeneousCubic (-185725440000) (-61908480000) (-126293299200000) 11503090851840000 p q

theorem bezout_p7 (p q : ℤ) :
    Up p q * numerator p q + Vp p q * denominator p q = 239541243494400000000 * p^7 := by
  unfold Up Vp numerator denominator F G homogeneousCubic homogeneousQuartic
  ring

theorem bezout_q7 (p q : ℤ) :
    Uq p q * numerator p q + Vq p q * denominator p q = 239541243494400000000 * q^7 := by
  unfold Uq Vq numerator denominator F G homogeneousCubic homogeneousQuartic
  ring

/-- All integer common divisors, with primitive integer coordinates. -/
theorem common_divisor_bound {p q d : ℤ} (hcop : IsCoprime p q)
    (hf : d ∣ numerator p q) (hg : d ∣ denominator p q) :
    d ∣ 239541243494400000000 :=
  common_divisor_of_bezout7 hcop hf hg (bezout_p7 p q) (bezout_q7 p q)

/-- Exact maximum of the numerator/denominator absolute coefficient sums. -/
theorem coefficient_C :
    max (coefficientAbsSum (FCoefficients (-1) (-408) 6912))
      (coefficientAbsSum (GCoefficients (-1) (-408) 6912)) = 250225 := by
  norm_num [coefficientAbsSum, FCoefficients, GCoefficients]

/-- Exact maximum of the two eight-coefficient witness absolute sums. -/
theorem coefficient_D :
    max (coefficientAbsSum [239541243494400000000, -482321205842411520000, -81856728512405176320000, 1555928294470944030720000, 120580301460602880000, -28281651243295703040000, 3041744714193331814400000, -10923913234098086215680000])
      (coefficientAbsSum [0, 742901760000, -495267840000, -404386191360000, -185725440000, -61908480000, -126293299200000, 11503090851840000]) = 15632567065268860354560000 := by
  norm_num [coefficientAbsSum]

end Branch1_5

namespace Branch1_10

def numerator (p q : ℤ) : ℤ := F 1 (-1633) 97763 p q
def denominator (p q : ℤ) : ℤ := G 1 (-1633) 97763 p q

def Up (p q : ℤ) : ℤ := homogeneousCubic 15179797184495846400000000 (-4799008765231452679680000) (-20283774628793344703493120000) 1329995609746680545126484480000 p q
def Vp (p q : ℤ) : ℤ := homogeneousCubic 1199752191307863169920000 (-7324560496133830272896640000) 2648748268340415778867113600000 (-7739602966810313911372394880000) p q
def Uq (p q : ℤ) : ℤ := homogeneousCubic 0 187014044160000 124676029440000 (-407254250165760000) p q
def Vq (p q : ℤ) : ℤ := homogeneousCubic (-46753511040000) 15584503680000 (-127247472547200000) 41187770487250560000 p q

theorem bezout_p7 (p q : ℤ) :
    Up p q * numerator p q + Vp p q * denominator p q = 15179797184495846400000000 * p^7 := by
  unfold Up Vp numerator denominator F G homogeneousCubic homogeneousQuartic
  ring

theorem bezout_q7 (p q : ℤ) :
    Uq p q * numerator p q + Vq p q * denominator p q = 15179797184495846400000000 * q^7 := by
  unfold Uq Vq numerator denominator F G homogeneousCubic homogeneousQuartic
  ring

/-- All integer common divisors, with primitive integer coordinates. -/
theorem common_divisor_bound {p q d : ℤ} (hcop : IsCoprime p q)
    (hf : d ∣ numerator p q) (hg : d ∣ denominator p q) :
    d ∣ 15179797184495846400000000 :=
  common_divisor_of_bezout7 hcop hf hg (bezout_p7 p q) (bezout_q7 p q)

/-- Exact maximum of the numerator/denominator absolute coefficient sums. -/
theorem coefficient_C :
    max (coefficientAbsSum (FCoefficients 1 (-1633) 97763))
      (coefficientAbsSum (GCoefficients 1 (-1633) 97763)) = 3061008 := by
  norm_num [coefficientAbsSum, FCoefficients, GCoefficients]

/-- Exact maximum of the two eight-coefficient witness absolute sums. -/
theorem coefficient_D :
    max (coefficientAbsSum [15179797184495846400000000, -4799008765231452679680000, -20283774628793344703493120000, 1329995609746680545126484480000, 1199752191307863169920000, -7324560496133830272896640000, 2648748268340415778867113600000, -7739602966810313911372394880000])
      (coefficientAbsSum [0, 187014044160000, 124676029440000, -407254250165760000, -46753511040000, 15584503680000, -127247472547200000, 41187770487250560000]) = 11745976358580478445504632320000 := by
  norm_num [coefficientAbsSum]

end Branch1_10

namespace Branch2_5

def numerator (p q : ℤ) : ℤ := F 1 (-1633) 32963 p q
def denominator (p q : ℤ) : ℤ := G 1 (-1633) 32963 p q

def Up (p q : ℤ) : ℤ := homogeneousCubic 42499768578278400000000 (-245570380220375354880000) (-62144670386170996945920000) 1485139046223011692423680000 p q
def Vp (p q : ℤ) : ℤ := homogeneousCubic 61392595055093838720000 (-19226286042676658202240000) 2750543590953410249385600000 (-28551598796459669094046080000) p q
def Uq (p q : ℤ) : ℤ := homogeneousCubic 0 9895426560000 6596951040000 (-21548940572160000) p q
def Vq (p q : ℤ) : ℤ := homogeneousCubic (-2473856640000) 824618880000 (-6733013155200000) 736604833080960000 p q

theorem bezout_p7 (p q : ℤ) :
    Up p q * numerator p q + Vp p q * denominator p q = 42499768578278400000000 * p^7 := by
  unfold Up Vp numerator denominator F G homogeneousCubic homogeneousQuartic
  ring

theorem bezout_q7 (p q : ℤ) :
    Uq p q * numerator p q + Vq p q * denominator p q = 42499768578278400000000 * q^7 := by
  unfold Uq Vq numerator denominator F G homogeneousCubic homogeneousQuartic
  ring

/-- All integer common divisors, with primitive integer coordinates. -/
theorem common_divisor_bound {p q d : ℤ} (hcop : IsCoprime p q)
    (hf : d ∣ numerator p q) (hg : d ∣ denominator p q) :
    d ∣ 42499768578278400000000 :=
  common_divisor_of_bezout7 hcop hf hg (bezout_p7 p q) (bezout_q7 p q)

/-- Exact maximum of the numerator/denominator absolute coefficient sums. -/
theorem coefficient_C :
    max (coefficientAbsSum (FCoefficients 1 (-1633) 32963))
      (coefficientAbsSum (GCoefficients 1 (-1633) 32963)) = 2801808 := by
  norm_num [coefficientAbsSum, FCoefficients, GCoefficients]

/-- Exact maximum of the two eight-coefficient witness absolute sums. -/
theorem coefficient_D :
    max (coefficientAbsSum [42499768578278400000000, -245570380220375354880000, -62144670386170996945920000, 1485139046223011692423680000, 61392595055093838720000, -19226286042676658202240000, 2750543590953410249385600000, -28551598796459669094046080000])
      (coefficientAbsSum [0, 9895426560000, 6596951040000, -21548940572160000, -2473856640000, 824618880000, -6733013155200000, 736604833080960000]) = 32869001852808792438597120000 := by
  norm_num [coefficientAbsSum]

end Branch2_5

end HeightCertificates
