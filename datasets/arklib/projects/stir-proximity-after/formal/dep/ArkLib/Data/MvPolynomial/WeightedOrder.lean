module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.MvPolynomial.Basic

@[expose] public section

noncomputable section

open Finsupp

open scoped Pointwise

namespace MvPolynomial

variable {σ τ R : Type*} [CommSemiring R]

/-- Coefficientwise projection onto the monomials whose exponents satisfy `p`. -/
def filterSupport (p : (σ →₀ ℕ) → Prop) [DecidablePred p] :
    MvPolynomial σ R →ₗ[R] MvPolynomial σ R where
  toFun F := AddMonoidAlgebra.ofCoeff (Finsupp.filter p (AddMonoidAlgebra.coeff F))
  map_add' F G := sorry
  map_smul' a F := sorry

/-- Truncation below `w`-weight `m`: keep exactly the monomials of weight less than `m`. -/
def weightedTruncation (w : σ → ℕ) (m : ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  filterSupport fun e => e.weight w < m

end MvPolynomial
