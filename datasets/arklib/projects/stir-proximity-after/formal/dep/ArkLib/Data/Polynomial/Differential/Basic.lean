module

public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import dep.ArkLib.Data.Polynomial.Differential.Types
public import dep.ArkLib.ToMathlib.Polynomial.HasseTaylor.FiniteJet

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open Polynomial

variable {F : Type*} {d : ℕ}

/-- Substitute `X`, a polynomial `P`, and its Hasse derivatives into a differential polynomial. -/
def differentialSpecializationHom [CommSemiring F] (P : F[X]) :
    DifferentialPolynomial F d →ₐ[F] F[X] :=
  MvPolynomial.aeval fun v : JetVariable d ↦ match v with
    | none => Polynomial.X
    | some j => Polynomial.hasseDeriv j P

/-- Apply `differentialSpecializationHom` to a differential polynomial. -/
def differentialSpecialization [CommSemiring F] (Q : DifferentialPolynomial F d) (P : F[X]) :
    F[X] :=
  differentialSpecializationHom P Q

/-- The scalar Hasse jet of `P` at `a`, through order `d`. -/
def polynomialJet [Semiring F] (a : F) (P : F[X]) : Fin (d + 1) → F :=
  Polynomial.hasseJet (d + 1) a P

end

end PolynomialDifferential
