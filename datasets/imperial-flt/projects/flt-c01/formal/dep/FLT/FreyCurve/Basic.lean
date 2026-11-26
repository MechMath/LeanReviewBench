module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Factors
public import Mathlib.NumberTheory.FLT.Basic
public import Mathlib.NumberTheory.FLT.Four
public import Mathlib.NumberTheory.FLT.Three
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Tactic.ModCases
public import dep.FLT.FreyCurve.FreyPackage

@[expose] public section

namespace FreyPackage

/-- The Weierstrass curve over `ℤ` associated to a Frey package. The conditions imposed
upon a Frey package guarantee that the running hypotheses in
Section 4.1 of [Serre] all hold. We put the curve into the form where the
equation is semistable at 2, rather than the usual `Y^2=X(X-a^p)(X+b^p)` form.
The change of variables is `X=4x` and `Y=8y+4x`, and then divide through by 64.
The fact that p is odd, a=3 mod 4 and b is even are enough to show that
this new curve still has coefficients in `ℤ`.
-/
def freyCurveInt (P : FreyPackage) : WeierstrassCurve ℤ where
  a₁ := 1
  -- Note that the numerator of a₂ is a multiple of 4
  a₂ := (P.b ^ P.p - 1 - P.a ^ P.p) / 4
  a₃ := 0
  a₄ := -(P.a ^ P.p) * (P.b ^ P.p) / 16 -- Note: numerator is multiple of 16
  a₆ := 0

/-- The elliptic curve over `ℚ` associated to a Frey package. The conditions imposed
upon a Frey package guarantee that the running hypotheses in
Section 4.1 of [Serre] all hold. We put the curve into the form where the
equation is semistable at 2, rather than the usual `Y^2=X(X-a^p)(X+b^p)` form.
The change of variables is `X=4x` and `Y=8y+4x`, and then divide through by 64. -/
def freyCurve (P : FreyPackage) : WeierstrassCurve ℚ where
  a₁ := 1
  -- a₂ is an integer because of the congruences assumed e.g. P.ha4
  a₂ := (P.b ^ P.p - 1 - P.a ^ P.p) / 4
  a₃ := 0
  a₄ := -(P.a ^ P.p) * (P.b ^ P.p) / 16 -- this is also an integer
  a₆ := 0

end FreyPackage

namespace FreyCurve

open FreyPackage WeierstrassCurve

theorem map (P : FreyPackage) : (freyCurveInt P).map (algebraMap ℤ ℚ) = freyCurve P := sorry

instance (P : FreyPackage) : WeierstrassCurve.IsElliptic (freyCurve P) := sorry

end FreyCurve
