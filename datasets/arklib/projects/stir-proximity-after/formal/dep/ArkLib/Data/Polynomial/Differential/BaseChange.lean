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
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.RingTheory.Polynomial.HilbertPoly
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import dep.ArkLib.Data.Polynomial.Differential.Basic
public import dep.ArkLib.Data.Polynomial.Differential.DerivativeDescent
public import dep.ArkLib.Data.Polynomial.Differential.JetDegree
public import dep.ArkLib.Data.Polynomial.Differential.JetPrefix
public import dep.ArkLib.Data.Polynomial.Differential.Types
public import dep.ArkLib.ToMathlib.MvPolynomial.ClearedSubstitution
public import dep.ArkLib.ToMathlib.MvPolynomial.PolynomialCoefficients
public import dep.ArkLib.ToMathlib.Polynomial.HasseTaylor.FiniteJet

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open Polynomial

variable {F E : Type*} {d : ℕ}

/-- Over a finite commutative semiring there are finitely many solutions of degree at most `D`:
a solution is determined by its `D + 1` coefficients. The degree bound is needed, since `F[X]`
is infinite whenever `F` is nontrivial. -/
instance BoundedSolution.instFinite [CommSemiring F] [Finite F] (Q : DifferentialPolynomial F d)
    (D : ℕ) : Finite (BoundedSolution Q D) := sorry

/-- Map a solution of `Q = 0` of degree at most `D` along `f` to a solution of `Q.map f = 0` of
degree at most `D`. -/
def BoundedSolution.map [CommSemiring F] [CommSemiring E] (f : F →+* E)
    {Q : DifferentialPolynomial F d} {D : ℕ} (P : BoundedSolution Q D) :
    BoundedSolution (MvPolynomial.map f Q) D :=
  ⟨⟨P.polynomial.map f, Polynomial.mem_degreeLT.mpr
      (Polynomial.degree_map_le.trans_lt (Polynomial.mem_degreeLT.mp P.1.2))⟩, sorry⟩

end

end PolynomialDifferential
