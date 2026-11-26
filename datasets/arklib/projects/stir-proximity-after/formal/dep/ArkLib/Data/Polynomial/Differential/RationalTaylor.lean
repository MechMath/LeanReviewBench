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

/-- A common separant exponent `τ` is sufficient for a length-`K` chart when it dominates the
denominator exponent `2(l - r) - 1` of every coefficient `c_l` with `l < K`. With natural
subtraction the exponent is zero for the initial coordinates `l ≤ r`. -/
def TaylorExponentSufficient (r K τ : ℕ) : Prop :=
  ∀ l : Fin K, 2 * (l.val - r) - 1 ≤ τ

section CommSemiring

variable {F : Type*} [CommSemiring F] {r : ℕ}

/-- The separant `∂Q/∂Y_r` with the independent variable set to `center`, as a polynomial in the
initial jet coordinates `Y_0, ..., Y_r`. -/
def initialJetSeparant (center : F) (Q : DifferentialPolynomial F r) :
    MvPolynomial (Fin (r + 1)) F :=
  aeval (fun i ↦ i.elim (C center) X) (separant Q (Fin.last r))

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] {r : ℕ}

end CommRing

variable {F : Type*} [Field F] {r : ℕ}

/-- The numerator of the rational Taylor coefficient `c_l`, a polynomial in the initial jet.

For `l ≤ r` it is the coordinate `Y_l`. For `l > r` it is
`-(l choose r)⁻¹` times the cleared substitution of the earlier numerators, with denominator
exponents `2(i - r) - 1` and budget `2(l - r) - 2`, into the coefficient of `ξ ^ (l - r)` of the
universal residual on the chart of length `l`. If `(l choose r) = 0` in `F`, the inverse is zero
and so is the numerator; the rational equations then hold only under the pivot hypothesis of
`rationalTaylorCoefficient_residual`. -/
def rationalTaylorNumerator (center : F) (Q : DifferentialPolynomial F r)
    (l : ℕ) : MvPolynomial (Fin (r + 1)) F :=
  if hl : l < r + 1 then X ⟨l, hl⟩ else
    -C ((l.choose r : F)⁻¹) *
      clearedSubstitution C (initialJetSeparant center Q)
        (fun i : Fin l ↦ rationalTaylorNumerator center Q i.val)
        (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2)
        ((optionEquivLeft F (Fin l) (universalTaylorResidual l center Q)).coeff (l - r))
termination_by l

/-- The rational Taylor coefficient `c_l` at an initial jet: the numerator evaluated at the jet,
divided by the separant at the jet to the power `2(l - r) - 1`. If the separant vanishes at the
jet, every coefficient with `l > r` is zero because division by zero is zero; the coefficients
are meaningful only where the separant is nonzero. -/
def rationalTaylorCoefficient (center : F) (Q : DifferentialPolynomial F r)
    (jet : Fin (r + 1) → F) (l : ℕ) : F :=
  aeval jet (rationalTaylorNumerator center Q l) /
    aeval jet (initialJetSeparant center Q) ^ (2 * (l - r) - 1)

end

end PolynomialDifferential
