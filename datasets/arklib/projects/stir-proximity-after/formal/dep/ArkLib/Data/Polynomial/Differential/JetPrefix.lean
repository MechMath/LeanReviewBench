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
public import dep.ArkLib.Data.Polynomial.Differential.JetDegree
public import dep.ArkLib.Data.Polynomial.Differential.Types
public import dep.ArkLib.ToMathlib.Polynomial.HasseTaylor.FiniteJet

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open Polynomial

variable {F : Type*} {d : ℕ}

/-- The polynomials of degree at most `D` that solve `Q = 0`. The degree bound is membership in
`Polynomial.degreeLT F (D + 1)`, which contains the zero polynomial. -/
def BoundedSolution [CommSemiring F] (Q : DifferentialPolynomial F d) (D : ℕ) :=
  {P : Polynomial.degreeLT F (D + 1) // differentialSpecialization Q P = 0}

/-- The polynomial underlying a bounded solution. -/
def BoundedSolution.polynomial [CommSemiring F] {Q : DifferentialPolynomial F d} {D : ℕ}
    (P : BoundedSolution Q D) : F[X] :=
  P.1

/-- A bounded solution solves `Q = 0`. -/
@[simp]
theorem BoundedSolution.equation [CommSemiring F] {Q : DifferentialPolynomial F d} {D : ℕ}
    (P : BoundedSolution Q D) : differentialSpecialization Q P.polynomial = 0 := sorry

/-- The inclusion of the variables `X, Y₀, ..., Y_s` of depth `s` into the variables of the
ambient depth `d`. -/
def jetPrefixEmbedding (s : Fin (d + 1)) : JetVariable s.val ↪ JetVariable d :=
  (Fin.castLEEmb s.isLt).optionMap

variable [CommSemiring F]

end

end PolynomialDifferential
