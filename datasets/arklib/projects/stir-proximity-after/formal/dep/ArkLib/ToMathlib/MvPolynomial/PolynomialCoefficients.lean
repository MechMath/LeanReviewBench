module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Combinatorics.Enumerative.InclusionExclusion
public import Mathlib.Data.Finsupp.PWO
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.Order
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
public import Mathlib.RingTheory.Polynomial.HilbertPoly
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import dep.ArkLib.ToMathlib.MvPolynomial.ClearedSubstitution

@[expose] public section

namespace MvPolynomial

noncomputable section

open scoped BigOperators

variable {R σ τ : Type*} [CommSemiring R]

/-- Every coefficient of `P : MvPolynomial σ R[X]` has `natDegree` at most `h`. -/
def CoeffNatDegreeLE (P : MvPolynomial σ (Polynomial R)) (h : ℕ) : Prop :=
  ∀ m, (P.coeff m).natDegree ≤ h

namespace CoeffNatDegreeLE

variable {P Q : MvPolynomial σ (Polynomial R)} {a b : ℕ}

/-- Sums keep a common coefficient degree bound. -/
theorem add (hP : CoeffNatDegreeLE P a) (hQ : CoeffNatDegreeLE Q a) :
    CoeffNatDegreeLE (P + Q) a := sorry

/-- Coefficient degree bounds add under products. -/
theorem mul (hP : CoeffNatDegreeLE P a) (hQ : CoeffNatDegreeLE Q b) :
    CoeffNatDegreeLE (P * Q) (a + b) := sorry

include R σ in
/-- The `n`-th power multiplies the coefficient degree bound by `n`. -/
theorem pow (hP : CoeffNatDegreeLE P a) (n : ℕ) : CoeffNatDegreeLE (P ^ n) (n * a) := sorry

/-- Substituting polynomials whose coefficients are constants keeps the coefficient degree
bound. -/
theorem aeval (hP : CoeffNatDegreeLE P a) (f : σ → MvPolynomial τ (Polynomial R))
    (hf : ∀ i, CoeffNatDegreeLE (f i) 0) : CoeffNatDegreeLE (MvPolynomial.aeval f P) a := sorry

include R in
/-- Formal differentiation keeps the coefficient degree bound. -/
theorem pderiv (hP : CoeffNatDegreeLE P a) (i : σ) :
    CoeffNatDegreeLE (MvPolynomial.pderiv i P) a := sorry

end CoeffNatDegreeLE

/-- Clearing a substitution preserves the coefficient-degree bound, with the denominator budget
`H` contributing at most `H * h` and the coefficients of `Q` contributing at most `a`. -/
theorem CoeffNatDegreeLE.clearedSubstitution
    {τ : Type*} (S : MvPolynomial σ (Polynomial R))
    (N : τ → MvPolynomial σ (Polynomial R)) (d : τ → ℕ) (H h a : ℕ)
    (Q : MvPolynomial τ (Polynomial R))
    (hS : CoeffNatDegreeLE S h)
    (hN : ∀ i, CoeffNatDegreeLE (N i) (d i * h))
    (hden : ∀ m ∈ Q.support, Finsupp.weight d m ≤ H)
    (hQ : ∀ m ∈ Q.support, (Q.coeff m).natDegree ≤ a) :
    CoeffNatDegreeLE (MvPolynomial.clearedSubstitution C S N d H Q) (H * h + a) := sorry

section CommRing

variable {A : Type*} [CommRing A]

end CommRing

end

end MvPolynomial
