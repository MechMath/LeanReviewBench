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
public import dep.ArkLib.Data.Polynomial.Differential.JetPrefix
public import dep.ArkLib.Data.Polynomial.Differential.Types
public import dep.ArkLib.ToMathlib.Polynomial.HasseTaylor.FiniteJet

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open Polynomial

variable {R : Type*} [CommSemiring R] {d : ℕ}

/-- A presentation of `Q` at depth `s`: a differential polynomial of depth `s` whose renaming
along `jetPrefixEmbedding s` is `Q`. -/
structure JetPrefixPresentation (Q : DifferentialPolynomial R d) (s : Fin (d + 1)) where
  /-- The depth-`s` differential polynomial. -/
  equation : DifferentialPolynomial R s.val
  /-- Renaming the depth-`s` polynomial into depth `d` gives `Q`. -/
  rename_equation : MvPolynomial.rename (jetPrefixEmbedding s) equation = Q

namespace JetPrefixPresentation

variable {Q : DifferentialPolynomial R d} {s : Fin (d + 1)}

/-- A presentation is unique, since the prefix renaming is injective. -/
instance instSubsingleton : Subsingleton (JetPrefixPresentation Q s) := sorry

/-- Mapping coefficients along `φ` maps a presentation of `Q` to a presentation of `Q.map φ`. -/
def map {S : Type*} [CommSemiring S] (φ : R →+* S) (A : JetPrefixPresentation Q s) :
    JetPrefixPresentation (MvPolynomial.map φ Q) s where
  equation := MvPolynomial.map φ A.equation
  rename_equation := sorry

end JetPrefixPresentation

end

end PolynomialDifferential
