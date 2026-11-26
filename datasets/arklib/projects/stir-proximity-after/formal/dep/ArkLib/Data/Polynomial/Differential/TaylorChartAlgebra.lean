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
public import dep.ArkLib.Data.Polynomial.Differential.TaylorChart
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

variable {A B : Type*} [CommSemiring A] [CommSemiring B] {r : ℕ}

variable {F : Type*} [Field F] {A B : Type*} [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B]

/-- The agreement equation over an `F`-algebra, with every common numerator using the same
separant exponent. -/
def taylorAgreementEquationOver (center : A) (Q : DifferentialPolynomial A r) (K : ℕ)
    (x y : A) (τ : ℕ) : MvPolynomial (Fin (r + 1)) A :=
  (∑ l : Fin K, C ((x - center) ^ l.val) *
    commonTaylorNumeratorOver F center Q τ l.val) - C y * initialJetSeparant center Q ^ τ

/-- The initial equation in joint challenge and initial-jet coordinates. -/
def jointInitialJetEquation {E : Type*} [CommSemiring E] (center : E)
    (Q : DifferentialPolynomial (Polynomial E) r) :
    MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E (Fin (r + 1))).symm
    (initialJetEquation (Polynomial.C center) Q)

/-- The initial separant in joint challenge and initial-jet coordinates. -/
def jointInitialJetSeparant {E : Type*} [CommSemiring E] (center : E)
    (Q : DifferentialPolynomial (Polynomial E) r) :
    MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E (Fin (r + 1))).symm
    (initialJetSeparant (Polynomial.C center) Q)

/-- A cleared Taylor coefficient in joint challenge and initial-jet coordinates. -/
def jointCommonTaylorNumerator {E : Type*} [Field E] (center : E)
    (Q : DifferentialPolynomial (Polynomial E) r)
    (τ : ℕ) {K : ℕ} (l : Fin K) : MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E (Fin (r + 1))).symm
    (commonTaylorNumeratorOver E (Polynomial.C center) Q τ l.val)

/-- The cleared agreement equation in joint challenge and initial-jet coordinates. -/
def jointTaylorAgreementEquation {E : Type*} [Field E] (center : E)
    (Q : DifferentialPolynomial (Polynomial E) r)
    (K τ : ℕ) (x y : Polynomial E) : MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E (Fin (r + 1))).symm
    (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K x y (τ := τ))

variable {E : Type*} [Field E]

end

end PolynomialDifferential
