module

public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Star.Basic
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

namespace CompPoly

namespace CBivariate

section ToPolyCore

/-- Convert `CBivariate R` to Mathlib's bivariate polynomial `R[X][Y]`.

  Maps each Y-coefficient through `CPolynomial.toPoly`, then builds
  `Polynomial (Polynomial R)` as the sum of monomials.
  -/
noncomputable def toPoly {R : Type*} [BEq R] [LawfulBEq R] [Semiring R]
    (p : CBivariate R) : R[X][Y] :=
  (CPolynomial.support p).sum (fun j ↦
    monomial j (CPolynomial.toPoly (p.val.coeff j)))

end ToPolyCore

section RingEquiv

end RingEquiv

section ImplementationCorrectness

end ImplementationCorrectness

end CBivariate

end CompPoly
