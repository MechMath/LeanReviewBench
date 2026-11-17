module

public import Mathlib.Algebra.BigOperators.Finsupp.Fin
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Data.Finsupp.Fin
public import dep.CompPoly.ToMathlib.Finsupp.Fin

@[expose] public section

namespace MvPolynomial

open Function Finsupp Polynomial

noncomputable section

section FinSuccEquivNth

variable {n : ℕ} {σ : Type*} (R : Type*) [CommSemiring R] (p : Fin (n + 1))

/-- The algebra isomorphism between multivariable polynomials in `Fin (n + 1)` and polynomials over
  multivariable polynomials in `Fin n`, where the `p`-th (pivot) variable is the indeterminate `X`.

  `finSuccEquiv` is the special case when `p = 0`. -/
def finSuccEquivNth : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R) :=
  (renameEquiv R (_root_.finSuccEquiv' p)).trans (optionEquivLeft R (Fin n))

variable {R} {p}

end FinSuccEquivNth

end

end MvPolynomial
