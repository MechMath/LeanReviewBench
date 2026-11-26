module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import dep.ArkLib.Data.Polynomial.Differential.Basic
public import dep.ArkLib.Data.Polynomial.Differential.JetDegree
public import dep.ArkLib.Data.Polynomial.Differential.Types
public import dep.ArkLib.ToMathlib.Polynomial.HasseTaylor.FiniteJet

@[expose] public section

open PolynomialDifferential

open scoped Polynomial

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {d : ℕ}

/-- The exponents of a source monomial `X^x Y₀^(y₀) ∏_j Y_(j+1)^(higher j)`. -/
structure SourceColumn (d : ℕ) where
  /-- The exponent of `X`. -/
  x : ℕ
  /-- The exponent of `Y₀`. -/
  y₀ : ℕ
  /-- The exponent of `Y_(j+1)`, for `j : Fin d`. -/
  higher : Fin d → ℕ

namespace SourceColumn

/-- The exponent vector of the source monomial of a column. -/
def exponent (c : SourceColumn d) : JetVariable d →₀ ℕ :=
  Finsupp.single none c.x + Finsupp.single (some 0) c.y₀ +
    ∑ j, Finsupp.single (some j.succ) (c.higher j)

variable {R : Type*} [CommSemiring R]

/-- The source monomial of a column, with coefficient `1`. -/
def polynomial (c : SourceColumn d) : DifferentialPolynomial R d :=
  monomial c.exponent 1

variable {κ : Type*} [Fintype κ]

end SourceColumn

end ReedSolomon.HiddenDerivative
