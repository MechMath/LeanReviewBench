module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import dep.ArkLib.Data.Polynomial.Differential.Basic
public import dep.ArkLib.Data.Polynomial.Differential.Types
public import dep.ArkLib.ToMathlib.Polynomial.HasseTaylor.FiniteJet

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open Polynomial

variable {F : Type*} {d D : ℕ}

/-- The individual degree in the formal Hasse variable `Y_j`. -/
def jetDegree [CommSemiring F] (Q : DifferentialPolynomial F d) (j : Fin (d + 1)) : ℕ :=
  Q.degreeOf (some j)

/-- Formal partial derivative of `Q` in the Hasse variable `Y_j`. -/
def separant [CommSemiring F] (Q : DifferentialPolynomial F d) (j : Fin (d + 1)) :
    DifferentialPolynomial F d :=
  MvPolynomial.pderiv (some j) Q

section CommSemiring

variable {R : Type*} [CommSemiring R] {r : ℕ}

open MvPolynomial

/-- The differential polynomial `Q` with the independent variable set to `center`, as a
polynomial in the initial jet coordinates `Y_0, ..., Y_r`. -/
def initialJetEquation (center : R) (Q : DifferentialPolynomial R r) :
    MvPolynomial (Fin (r + 1)) R :=
  MvPolynomial.aeval (fun i ↦ i.elim (C center) X) Q

end CommSemiring

end

end PolynomialDifferential
