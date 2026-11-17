module

public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Tropical.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Lattice.Nat
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Tactic.Cases
public import dep.CompPoly.Data.Array.Lemmas
public import dep.CompPoly.Univariate.Raw.Core
public import dep.CompPoly.Univariate.Raw.Division
public import dep.CompPoly.Univariate.Raw.Ops

public section

namespace CompPoly

namespace CPolynomial.Raw

variable {R : Type*}

variable {Q : Type*}

section Operations

section Semiring

variable [Semiring R] [BEq R]

variable [Semiring Q]

variable {S : Type*}

variable (p q r : CPolynomial.Raw R)

section AddDefs

end AddDefs

section AddTheorems

theorem add_comm : p + q = q + p := sorry

theorem monomial_canonical [LawfulBEq R] [DecidableEq R] (n : ℕ) (c : R) :
    (monomial n c).trim = monomial n c := sorry

theorem X_canonical [Nontrivial R] [LawfulBEq R] : X.trim = (X : CPolynomial.Raw R) := sorry

theorem add_assoc [LawfulBEq R] : p + q + r = p + (q + r) := sorry

end AddTheorems

section MulInfrastructure

section MulOneTrimHelpers

end MulOneTrimHelpers

section MulAssocSumHelpers

end MulAssocSumHelpers

end MulInfrastructure

section SMulTheorems

end SMulTheorems

section MulPowXLemmas

end MulPowXLemmas

section MulInfrastructure

section MulCoeffHelpers

theorem mul_is_trimmed [LawfulBEq R] (p q : CPolynomial.Raw R) : (p * q).trim = p * q := sorry

/-- `Raw.add` trims at the end of its accumulation, so its output is canonical. -/
theorem add_is_trimmed [LawfulBEq R] (p q : CPolynomial.Raw R) : (p + q).trim = p + q := sorry

namespace MulLowContext

end MulLowContext

namespace MulLowContext

end MulLowContext

end MulCoeffHelpers

end MulInfrastructure

section MulTheorems

end MulTheorems

section EvalTheorems

variable [Semiring S]

/-- Compiled code evaluates by Horner's method; `eval₂` remains the specification. -/
@[csimp]
theorem eval₂_eq_eval₂Horner : @eval₂ = @eval₂Horner := sorry

/-- Compiled code evaluates by Horner's method; `eval` remains the specification.
`eval` is `@[inline]`, so without this callers would inline its sum-of-powers body. -/
@[csimp]
theorem eval_eq_evalHorner : @eval = @evalHorner := sorry

end EvalTheorems

end Semiring

section CommutativeSemiring

variable [CommSemiring R] [BEq R]

end CommutativeSemiring

section Ring

variable [Ring R] [BEq R]

theorem neg_trim [LawfulBEq R] (p : CPolynomial.Raw R) : p.trim = p → (-p).trim = -p := sorry

end Ring

section DivisionTheorems

variable [BEq R]

section

variable [CommRing R] [Nontrivial R]

end

section

variable [Field R]

end

section

variable [CommRing R]

end

section

variable [Field R]

/-- `Raw.div` returns a canonical polynomial (no condition on inputs). -/
theorem div_canonical [LawfulBEq R] (p q : CPolynomial.Raw R) :
    (div p q).trim = div p q := sorry

/-- `Raw.mod` returns a canonical polynomial (no condition on inputs).
The intermediate `C (q.leadingCoeff)⁻¹ • p` is `C _ * p` via `Mul.toSMul`, which trims. -/
theorem mod_canonical [LawfulBEq R] (p q : CPolynomial.Raw R) :
    (mod p q).trim = mod p q := sorry

end

end DivisionTheorems

end Operations

section AddCommSemigroup

variable [Semiring R] [BEq R]

instance [LawfulBEq R] : AddCommSemigroup (CPolynomial.Raw R) where
  add_assoc := sorry
  add_comm := add_comm

end AddCommSemigroup

section RepeatedSquaring

variable [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]

end RepeatedSquaring

end CPolynomial.Raw

end CompPoly
