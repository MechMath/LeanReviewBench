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
public import dep.ArkLib.Data.Polynomial.Differential.RationalTaylor
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

variable (F : Type*) {A B : Type*} [Field F] [CommRing A] [CommRing B] [Algebra F A] {r : ℕ}

/-- The numerator of the rational Taylor coefficient `c_l` over an `F`-algebra `A`, a polynomial
in the initial jet with coefficients in `A`.

For `l ≤ r` it is the coordinate `Y_l`. For `l > r` it is `-(l choose r)⁻¹` times the cleared
substitution of the earlier numerators, with denominator exponents `2(i - r) - 1` and budget
`2(l - r) - 2`, into the coefficient of `ξ ^ (l - r)` of the universal residual on the chart of
length `l`. The inverse `(l choose r)⁻¹` is taken in `F`, and it is zero when `(l choose r) = 0`
in `F`. -/
def rationalTaylorNumeratorOver (center : A) (Q : DifferentialPolynomial A r)
    (l : ℕ) : MvPolynomial (Fin (r + 1)) A :=
  if hl : l < r + 1 then X ⟨l, hl⟩ else
    -C (algebraMap F A ((l.choose r : F)⁻¹)) *
      clearedSubstitution C (initialJetSeparant center Q)
        (fun i : Fin l ↦ rationalTaylorNumeratorOver center Q i.val)
        (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2)
        ((optionEquivLeft A (Fin l) (universalTaylorResidual l center Q)).coeff (l - r))
termination_by l

/-- The numerator of `c_l` padded to the common denominator `S ^ τ`, where `S` is the initial
separant: `rationalTaylorNumeratorOver F center Q l * S ^ (τ - (2(l - r) - 1))`. The padding is
exact when `2(l - r) - 1 ≤ τ`; otherwise natural subtraction truncates it. -/
def commonTaylorNumeratorOver (center : A) (Q : DifferentialPolynomial A r) (τ l : ℕ) :
    MvPolynomial (Fin (r + 1)) A :=
  rationalTaylorNumeratorOver F center Q l *
    initialJetSeparant center Q ^ (τ - (2 * (l - r) - 1))

end

end PolynomialDifferential
