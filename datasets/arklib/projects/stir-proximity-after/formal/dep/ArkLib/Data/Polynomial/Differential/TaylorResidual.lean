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
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.RingTheory.Finiteness.Basic
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
public import Mathlib.Tactic.Ring
public import dep.ArkLib.Data.Polynomial.Differential.Basic
public import dep.ArkLib.Data.Polynomial.Differential.JetDegree
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

variable {F : Type*} [CommSemiring F]

/-- The `j`-th Hasse derivative of `∑ l < K, c_l ξ ^ l`, as a polynomial in the displacement
`ξ` (variable `none`) and the symbolic coefficients `c_l` (variable `some l`). It is
`∑ l ≥ j, (l choose j) c_l ξ ^ (l - j)`. -/
def universalTaylorJet (K j : ℕ) : MvPolynomial (Option (Fin K)) F :=
  ∑ l ∈ Finset.univ.filter (fun l : Fin K ↦ j ≤ l.val),
    monomial (Finsupp.single (some l) 1 + Finsupp.single none (l.val - j))
      (Nat.choose l.val j : F)

/-- The universal residual of an order-`r` differential polynomial `Q` along a length-`K` Taylor
chart at `center`. The independent variable becomes `center + ξ` and the jet variable `Y_j`
becomes `universalTaylorJet K j`. -/
def universalTaylorResidual {r : ℕ} (K : ℕ) (center : F)
    (Q : DifferentialPolynomial F r) : MvPolynomial (Option (Fin K)) F :=
  aeval (fun i ↦ i.elim (C center + X none) (fun j ↦ universalTaylorJet K j.val)) Q

section Map

variable {A B : Type*} [CommSemiring A] [CommSemiring B]

end Map

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

end CommRing

end

end PolynomialDifferential
