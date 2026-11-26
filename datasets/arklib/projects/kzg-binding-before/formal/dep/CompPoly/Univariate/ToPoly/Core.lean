module

public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.Algebra.Tropical.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Lattice.Nat
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Tactic.Cases
public import dep.CompPoly.Data.Array.Lemmas
public import dep.CompPoly.Univariate.Basic
public import dep.CompPoly.Univariate.Linear
public import dep.CompPoly.Univariate.Raw.Core
public import dep.CompPoly.Univariate.Raw.Division
public import dep.CompPoly.Univariate.Raw.Ops
public import dep.CompPoly.Univariate.Raw.Proofs

public section

open Polynomial

namespace CompPoly

namespace CPolynomial

open Raw

variable {R : Type*}

variable {Q : Type*}

section ToPolyDefs

/-- Convert a `CPolynomial.Raw` to a (mathlib) `Polynomial`. -/
noncomputable def Raw.toPoly [Semiring R] (p : CPolynomial.Raw R) : Polynomial R :=
  p.eval₂ Polynomial.C Polynomial.X

/-- Convert a canonical polynomial to a (mathlib) `Polynomial`. -/
@[coe] noncomputable def toPoly [Semiring R] (p : CPolynomial R) : Polynomial R := p.val.toPoly

/-- `toPoly` is the coercion to Mathlib's `Polynomial`, so `norm_cast`, `push_cast` and
`exact_mod_cast` transfer statements across it. -/
noncomputable instance [Semiring R] : Coe (CPolynomial R) (Polynomial R) := ⟨toPoly⟩

end ToPolyDefs

section ToPoly

variable [Semiring R] [BEq R]

variable [Semiring Q]

namespace Raw

end Raw

end ToPoly

end CPolynomial

end CompPoly
