module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.MvPolynomial.Basic
public import dep.ArkLib.Data.CodingTheory.HiddenDerivative.Variables
public import dep.ArkLib.Data.Polynomial.Differential.Types

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R] {d : ℕ}

/-- The signed correction that appears directly in `Y₀`, `∑_{r<d} (-1)^r T^(r+1) Y_(r+1)`. -/
def localCorrection (d : ℕ) : LocalPolynomial R d :=
  ∑ j : Fin d, C ((-1 : R) ^ j.val) * X (localT d) ^ (j.val + 1) * X (localY j)

/-- Generator images of the complete unscaled local substitution. -/
def unscaledLocalImage (d : ℕ) (center received : R) : JetVariable d → LocalPolynomial R d
  | none => C center + X (localT d)
  | some j => Fin.cases (C received + localCorrection d + X (localT d) * X (localE d))
      (fun highOrder => X (localY highOrder)) j

/-- The complete unscaled local substitution. Its error variable `E` appears only as `T E`. -/
def unscaledLocalSubstitution (d : ℕ) (center received : R) :
    DifferentialPolynomial R d →ₐ[R] LocalPolynomial R d :=
  bind₁ (unscaledLocalImage d center received)

end ReedSolomon.HiddenDerivative
