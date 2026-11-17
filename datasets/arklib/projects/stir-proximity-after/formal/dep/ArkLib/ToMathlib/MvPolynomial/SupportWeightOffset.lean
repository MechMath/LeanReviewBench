module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

@[expose] public section

namespace MvPolynomial

noncomputable section

variable {R σ τ : Type*} [CommSemiring R]

/-- Every monomial `m` of `p` has first weight at most its second weight plus the allowance `d`:
`a m ≤ b m + d`. -/
def SupportWeightOffset (a b : (σ →₀ ℕ) →+ ℕ) (d : ℕ)
    (p : MvPolynomial σ R) : Prop := ∀ m ∈ p.support, a m ≤ b m + d

namespace SupportWeightOffset

variable {a b : (σ →₀ ℕ) →+ ℕ} {d e : ℕ} {p q : MvPolynomial σ R}

/-- A monomial has allowance `d` when its exponent does. The coefficient is arbitrary; a zero
coefficient gives the zero polynomial. -/
theorem monomial (m : σ →₀ ℕ) (r : R) (h : a m ≤ b m + d) :
    SupportWeightOffset a b d (MvPolynomial.monomial m r) := sorry

/-- A constant has every allowance, since both weights vanish on the zero exponent. -/
theorem C (r : R) : SupportWeightOffset a b d (MvPolynomial.C r) := sorry

/-- Sums keep a common allowance. -/
theorem add (hp : SupportWeightOffset a b d p) (hq : SupportWeightOffset a b d q) :
    SupportWeightOffset a b d (p + q) := sorry

/-- Allowances add under multiplication, because both weights are additive and every monomial of
`p * q` is a sum of a monomial of `p` and a monomial of `q`. -/
theorem mul (hp : SupportWeightOffset a b d p) (hq : SupportWeightOffset a b e q) :
    SupportWeightOffset a b (d + e) (p * q) := sorry

include R in
/-- The `n`-th power multiplies the allowance by `n`. -/
theorem pow (hp : SupportWeightOffset a b d p) (n : ℕ) :
    SupportWeightOffset a b (n * d) (p ^ n) := sorry

/-- Finite sums keep a common allowance. -/
theorem sum {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ R)
    (hp : ∀ i ∈ s, SupportWeightOffset a b d (p i)) :
    SupportWeightOffset a b d (∑ i ∈ s, p i) := sorry

/-- A finite product has the sum of the allowances of its factors. -/
theorem prod {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ R) (d : ι → ℕ)
    (hp : ∀ i ∈ s, SupportWeightOffset a b (d i) (p i)) :
    SupportWeightOffset a b (∑ i ∈ s, d i) (∏ i ∈ s, p i) := sorry

end SupportWeightOffset

end

end MvPolynomial
