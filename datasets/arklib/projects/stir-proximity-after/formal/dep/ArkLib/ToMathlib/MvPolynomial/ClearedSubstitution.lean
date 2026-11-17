module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

namespace MvPolynomial

noncomputable section

open scoped BigOperators

variable {F R E τ : Type*} [CommSemiring F] [CommSemiring R] [Field E]

/-- The cleared numerator `∑ m ∈ Q.support, f (Q.coeff m) * ∏ i, N i ^ m i * S ^ (H - w m)`,
where `w m = ∑ i, d i * m i` is the denominator weight of `m`.

When every monomial of `Q` has `w m ≤ H`, this is `S ^ H` times `Q` evaluated at
`N i / S ^ d i` (`map_clearedSubstitution`). Without that hypothesis, natural subtraction truncates
`H - w m` to zero on the monomials that exceed the budget, and the identity fails. -/
def clearedSubstitution (f : F →+* R) (S : R) (N : τ → R) (d : τ → ℕ)
    (H : ℕ) (Q : MvPolynomial τ F) : R :=
  ∑ m ∈ Q.support, f (Q.coeff m) *
    (∏ i ∈ m.support, N i ^ m i) * S ^ (H - Finsupp.weight d m)

end

end MvPolynomial
