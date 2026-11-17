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

variable {F : Type*} {d : ℕ} [CommSemiring F]

/-- Every positive integer `k ≤ jetDegree Q s` is nonzero in `F`.

This is the hypothesis under which differentiating `Q` in `Y_s` up to `jetDegree Q s` times loses
exactly one degree in `Y_s` per derivative: the `k`-th derivative multiplies the leading
coefficient by the current degree `jetDegree Q s - k + 1`. It holds in characteristic zero, and in
characteristic `p > 0` when `jetDegree Q s < p` (see `jetDegreeCastsNeZero_of_ringChar`). It holds
trivially when `Q` does not depend on `Y_s`. -/
def JetDegreeCastsNeZero (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) : Prop :=
  ∀ k : ℕ, 0 < k → k ≤ jetDegree Q s → (k : F) ≠ 0

/-- The cast hypothesis in the form used by
`MvPolynomial.degreeOf_iterate_pderiv_eq_sub_of_natCast_ne_zero`. -/
private theorem JetDegreeCastsNeZero.sub {Q : DifferentialPolynomial F d} {s : Fin (d + 1)}
    (h : JetDegreeCastsNeZero Q s) {a : ℕ} (ha : a ≤ jetDegree Q s) :
    ∀ k < a, ((Q.degreeOf (some s) - k : ℕ) : F) ≠ 0 := sorry

end

end PolynomialDifferential
