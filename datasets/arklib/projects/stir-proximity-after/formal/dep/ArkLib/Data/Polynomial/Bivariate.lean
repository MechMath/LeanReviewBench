module

public import Aesop
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.Algebra.Tropical.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Lattice.Nat
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Tactic.Cases
public import dep.CompPoly.Bivariate.Basic
public import dep.CompPoly.Bivariate.ToPoly
public import dep.CompPoly.Data.Array.Lemmas
public import dep.CompPoly.ToMathlib.Polynomial.BivariateDegree
public import dep.CompPoly.ToMathlib.Polynomial.BivariateWeightedDegree
public import dep.CompPoly.Univariate.Basic
public import dep.CompPoly.Univariate.Linear
public import dep.CompPoly.Univariate.Raw.Core
public import dep.CompPoly.Univariate.Raw.Division
public import dep.CompPoly.Univariate.Raw.Ops
public import dep.CompPoly.Univariate.Raw.Proofs
public import dep.CompPoly.Univariate.ToPoly.Core

@[expose] public section

open Polynomial

open Polynomial.Bivariate

namespace Polynomial.Bivariate

noncomputable section

variable {F : Type} [Semiring F]

/-- The set of coefficients of a bivariate polynomial. -/
def coeffs [DecidableEq F] (f : F[X][Y]) : Finset F[X] := f.support.image f.coeff

variable {f : F[X][Y]}

attribute [local grind] Finsupp.support_nonempty_iff natDegree_mul_le degree_eq_bot
                        WithBot.bot_lt_coe isMaxOn_iff sup_eq_of_isMaxOn monomial_eq_monomial_iff

attribute [local grind ←] toFinsupp_eq_zero

attribute [local grind _=_] Finsupp.mem_support_iff toFinsupp_apply smul_monomial

attribute [local grind =] natDegree_mul natDegree_add_eq_right_of_degree_lt
                          natDegree_zero

end

end Polynomial.Bivariate
