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
public import Mathlib.Tactic.Cases
public import dep.CompPoly.Bivariate.Basic
public import dep.CompPoly.Bivariate.ToPoly
public import dep.CompPoly.Data.Array.Lemmas
public import dep.CompPoly.Univariate.Basic
public import dep.CompPoly.Univariate.Linear
public import dep.CompPoly.Univariate.Raw.Core
public import dep.CompPoly.Univariate.Raw.Division
public import dep.CompPoly.Univariate.Raw.Ops
public import dep.CompPoly.Univariate.Raw.Proofs
public import dep.CompPoly.Univariate.ToPoly.Core

@[expose] public section

open Polynomial

open scoped Polynomial.Bivariate

namespace Polynomial.Bivariate

noncomputable section

variable {F : Type*}

section Semiring

variable [Semiring F]

/-- `(i, j)`-coefficient of a polynomial, i.e. the coefficient of `X^i Y^j`. -/
def coeff (f : F[X][Y]) (i j : ℕ) : F :=
  (f.coeff j).coeff i

variable {f : F[X][Y]}

end Semiring

section CommSemiring

variable [CommSemiring F]

end CommSemiring

section CommRing

variable [CommRing F]

end CommRing

section Field

variable [Field F] [DecidableEq F]

end Field

end

end Polynomial.Bivariate

namespace CompPoly

namespace CBivariate

end CBivariate

end CompPoly
