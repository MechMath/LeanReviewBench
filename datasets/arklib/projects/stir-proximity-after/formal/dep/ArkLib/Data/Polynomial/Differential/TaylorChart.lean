module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Combinatorics.Enumerative.InclusionExclusion
public import Mathlib.Data.Finsupp.PWO
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Groebner
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.RingTheory.Polynomial.HilbertPoly
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import dep.ArkLib.Data.Polynomial.Differential.Basic
public import dep.ArkLib.Data.Polynomial.Differential.JetDegree
public import dep.ArkLib.Data.Polynomial.Differential.RationalTaylor
public import dep.ArkLib.Data.Polynomial.Differential.RationalTaylorAlgebra
public import dep.ArkLib.Data.Polynomial.Differential.TaylorResidual
public import dep.ArkLib.Data.Polynomial.Differential.Types
public import dep.ArkLib.Data.Polynomial.TaylorPrefix
public import dep.ArkLib.ToMathlib.MvPolynomial.ClearedSubstitution
public import dep.ArkLib.ToMathlib.MvPolynomial.PolynomialCoefficients
public import dep.ArkLib.ToMathlib.Polynomial.HasseTaylor.FiniteJet

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

open scoped BigOperators

section CommSemiring

variable {R : Type*} [CommSemiring R] {r : ℕ}

end CommSemiring

variable {F : Type*} [Field F] {r : ℕ}

/-- The numerator of the rational Taylor coefficient `c_l` over the common denominator `S ^ τ`,
where `S` is the initial separant: `rationalTaylorNumerator center Q l * S ^ (τ - (2(l - r) - 1))`.
It represents `S ^ τ * c_l` when `2(l - r) - 1 ≤ τ`. -/
def commonTaylorNumerator (center : F) (Q : DifferentialPolynomial F r) (τ l : ℕ) :
    MvPolynomial (Fin (r + 1)) F :=
  rationalTaylorNumerator center Q l * initialJetSeparant center Q ^ (τ - (2 * (l - r) - 1))

/-- The polynomial of degree below `K` whose Taylor coefficients at `center` are the first `K`
rational Taylor coefficients of `jet`. -/
def rationalTaylorPolynomial (center : F) (Q : DifferentialPolynomial F r) (K : ℕ)
    (jet : Fin (r + 1) → F) : Polynomial F :=
  Polynomial.centeredCoefficientPrefix center (rationalTaylorCoefficient center Q jet) K

end

end PolynomialDifferential
