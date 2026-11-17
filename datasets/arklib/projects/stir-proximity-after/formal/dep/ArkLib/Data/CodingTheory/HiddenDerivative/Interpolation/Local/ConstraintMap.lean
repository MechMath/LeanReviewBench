module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import dep.ArkLib.Data.CodingTheory.HiddenDerivative.Substitution
public import dep.ArkLib.Data.CodingTheory.HiddenDerivative.Variables
public import dep.ArkLib.Data.MvPolynomial.WeightedOrder
public import dep.ArkLib.Data.Polynomial.Differential.Basic
public import dep.ArkLib.Data.Polynomial.Differential.JetDegree
public import dep.ArkLib.Data.Polynomial.Differential.Types
public import dep.ArkLib.ToMathlib.Polynomial.HasseTaylor.FiniteJet

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R]

variable {d D A M W : ℕ}

/-- Keep the monomials of contact order below `m`. -/
def projectLowContact (m : ℕ) : LocalPolynomial R d →ₗ[R] LocalPolynomial R d :=
  weightedTruncation (localContactWeight d) m

/-- The local constraint map at `(center, received)`: the low-contact part of the unscaled local
substitution. -/
def localConstraintAt (m : ℕ) (center received : R) :
    DifferentialPolynomial R d →ₗ[R] LocalPolynomial R d :=
  (projectLowContact m).comp (unscaledLocalSubstitution d center received).toLinearMap

/-- `Q` satisfies the local constraints of multiplicity `m` at `(center, received)`: after the
unscaled local substitution, every monomial of contact order below `m` has coefficient zero. -/
def SatisfiesLocalConstraints (m : ℕ) (center received : R)
    (Q : DifferentialPolynomial R d) : Prop :=
  localConstraintAt m center received Q = 0

/-- Local constraints are preserved by every coefficient-ring homomorphism. -/
theorem SatisfiesLocalConstraints.map {S : Type*} [CommRing S] (φ : R →+* S) (m : ℕ)
    (center received : R) (Q : DifferentialPolynomial R d)
    (hQ : SatisfiesLocalConstraints m center received Q) :
    SatisfiesLocalConstraints m (φ center) (φ received) (MvPolynomial.map φ Q) := sorry

end ReedSolomon.HiddenDerivative
