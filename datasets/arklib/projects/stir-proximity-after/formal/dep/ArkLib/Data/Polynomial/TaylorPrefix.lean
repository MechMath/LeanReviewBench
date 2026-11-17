module

public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import dep.ArkLib.ToMathlib.Polynomial.HasseTaylor.FiniteJet

@[expose] public section

open scoped BigOperators

namespace Polynomial

noncomputable section

variable {R : Type*} [CommRing R]

/-- The degree-`< K` polynomial whose first `K` Hasse coefficients at `center` are `c 0`, ...,
`c (K - 1)`.

The finite sum is first formed in the displacement variable and then translated back to the
original variable. -/
def centeredCoefficientPrefix (center : R) (c : ℕ → R) (K : ℕ) : R[X] :=
  taylor (-center) (∑ i : Fin K, monomial i.val (c i.val))

end

end Polynomial
