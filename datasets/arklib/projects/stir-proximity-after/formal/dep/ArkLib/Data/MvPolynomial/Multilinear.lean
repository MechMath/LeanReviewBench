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
public import dep.ArkLib.Data.MvPolynomial.Interpolation

@[expose] public section

noncomputable section

namespace MvPolynomial

open BigOperators Fintype Finset

universe u

variable {σ : Type*} {R : Type*}

instance coeFunctionFin2 [NatCast R] : Coe (σ → Fin 2) (σ → R) where
  coe := fun vec i => vec i

variable [CommRing R]

variable [Fintype σ]

variable [DecidableEq σ]

section DegreeOf

end DegreeOf

variable [DecidableEq R] [IsDomain R]

end MvPolynomial

end
