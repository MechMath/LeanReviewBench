module

public import Mathlib.Algebra.BigOperators.Finsupp.Fin
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.FinEnum
public import Mathlib.Data.Finsupp.Fin
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.Basic

@[expose] public section

noncomputable section

namespace MvPolynomial

open Finset

section SchwartzZippel

variable {σ : Type*} [DecidableEq σ]

variable {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]

end SchwartzZippel

section Vars

variable {σ : Type*}

instance (s : Finset σ) : Fintype { x : σ | x ∈ s } := by exact Set.fintypeMemFinset s

end Vars

section MvPolynomialDetermination

variable {σ : Type*} [DecidableEq σ] [Fintype σ]

variable {R : Type*} [CommRing R] [IsDomain R]

section Finset

open Fintype

variable {n : ℕ}

open Polynomial

end Finset

end MvPolynomialDetermination

end MvPolynomial

end
