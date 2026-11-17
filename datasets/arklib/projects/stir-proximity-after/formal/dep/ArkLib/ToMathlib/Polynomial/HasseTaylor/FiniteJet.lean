module

public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.RingTheory.Polynomial.DegreeLT

@[expose] public section

namespace Polynomial

noncomputable section

variable {R : Type*}

section Semiring

variable [Semiring R]

/-- The `i`-th Hasse coefficient of `p` at `r`, packaged as a linear functional.

Equivalently, this is coefficient `i` of `p(X + r)`. -/
def hasseCoeffAt (r : R) (i : ℕ) : R[X] →ₗ[R] R :=
  (leval r).comp (hasseDeriv i)

/-- The first `m` Hasse coefficients of a polynomial at `r`.

Index `i : Fin m` records `D⁽ⁱ⁾ p(r)`, where `D⁽ⁱ⁾` is the Hasse derivative.  Thus
`m = 0` gives the empty jet and `m = 1` records only evaluation at `r`. -/
def hasseJet (m : ℕ) (r : R) : R[X] →ₗ[R] (Fin m → R) where
  toFun p i := hasseCoeffAt r i p
  map_add' p q := sorry
  map_smul' c p := sorry

end Semiring

section CommSemiring

variable [CommSemiring R]

end CommSemiring

section CommRing

variable [CommRing R]

end CommRing

end

end Polynomial
