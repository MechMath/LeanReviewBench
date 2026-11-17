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

public section

open Polynomial

namespace CompPoly

/-- A type analogous to `Polynomial` that supports computable operations. This is defined to be a
  wrapper around `Array`.

  For example, the Array `#[1,2,3]` represents the polynomial `1 + 2x + 3x^2`.
  Two arrays may represent the same polynomial via zero-padding,
  for example `#[1,2,3] = #[1,2,3,0,0,0,...]`.
-/
@[expose, reducible, inline, specialize]
def CPolynomial.Raw (R : Type*) := Array R

namespace CPolynomial.Raw

/-- Construct a `CPolynomial.Raw` from an array of coefficients. -/
@[expose, reducible]
def mk {R : Type*} (coeffs : Array R) : CPolynomial.Raw R := coeffs

/-- Extract the underlying array of coefficients. -/
@[expose, reducible]
def coeffs {R : Type*} (p : CPolynomial.Raw R) : Array R := p

variable {R : Type*}

variable {Q : Type*}

section Foundations

/-- The coefficient of `X^i` in the polynomial. Returns `0` if `i` is out of bounds. -/
@[reducible]
def coeff [Zero R] (p : CPolynomial.Raw R) (i : ℕ) : R := p.getD i 0

/-- The constant polynomial `C r`. -/
def C (r : R) : CPolynomial.Raw R := #[r]

/-- The variable `X`. -/
def X [Zero R] [One R] : CPolynomial.Raw R := #[0, 1]

/-- Construct a monomial `c * X^n` as a `CPolynomial.Raw R`.

  The result is an array with `n` zeros followed by `c`.
  For example, `monomial 2 3` = `#[0, 0, 3]` represents `3 * X^2`.

  Note: If `c = 0`, this returns `#[]` (the zero polynomial).
-/
def monomial [Zero R] [DecidableEq R] (n : ℕ) (c : R) : CPolynomial.Raw R :=
  if c = 0 then #[] else .mk (Array.replicate n 0 ++ #[c])

/-- Return the index of the last non-zero coefficient of a `CPolynomial.Raw` -/
def lastNonzero [Zero R] [BEq R] (p : CPolynomial.Raw R) : Option (Fin p.size) :=
  p.findIdxRev? (· != 0)

/-- Remove trailing zeroes from a `CPolynomial.Raw`.
Requires `BEq` to check if the coefficients are zero. -/
def trim [Zero R] [BEq R] (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  match p.lastNonzero with
  | none => #[]
  | some i => p.extract 0 (i.val + 1)

/-- Return the degree of a `CPolynomial.Raw`. -/
def degree [Zero R] [BEq R] (p : CPolynomial.Raw R) : WithBot ℕ :=
  match p.lastNonzero with
  | none => ⊥
  | some i => i.val

/-- Natural number degree of a `CPolynomial.Raw`.

  Returns the degree as a natural number. For the zero polynomial, returns `0`.
  This matches Mathlib's `Polynomial.natDegree` API.
-/
def natDegree [Zero R] [BEq R] (p : CPolynomial.Raw R) : ℕ :=
  match p.lastNonzero with
  | none => 0
  | some i => i.val

/-- Return the leading coefficient of a `CPolynomial.Raw` as the last coefficient
of the trimmed array, or `0` if the trimmed array is empty. -/
def leadingCoeff [Zero R] [BEq R] (p : CPolynomial.Raw R) : R := p.trim.getLastD 0

/-- Semantic canonicality for raw coefficient arrays: a polynomial is canonical iff its
last stored coefficient, when present, is nonzero. This invariant is independent of any
particular `BEq` instance. -/
def IsCanonical [Zero R] (p : CPolynomial.Raw R) : Prop :=
  ∀ hp : p.size > 0, p.getLast hp ≠ 0

namespace Trim

/-- eliminator for `p.trim`; e.g. use for case distinction as follows:
  ```
  rcases (Trim.elim p) with ⟨ h_empty, h_all_zero ⟩ | ⟨ k, h_extract, h_nonzero, h_max ⟩
  ```
-/
theorem elim [Zero R] [BEq R] [LawfulBEq R] (p : CPolynomial.Raw R) :
    (p.trim = #[] ∧  (∀ i, (hi : i < p.size) → p[i] = 0))
    ∨ (∃ k : Fin p.size,
        p.trim = p.extract 0 (k + 1)
      ∧ p[k] ≠ 0
      ∧ (∀ j : ℕ, (hj : j < p.size) → j > k → p[j] = 0)) := sorry

attribute [simp] Array.getElem?_eq_none

/-- Equivalence relation: two polynomials are equivalent if all coefficients agree. -/
def equiv [Zero R] (p q : CPolynomial.Raw R) : Prop :=
  ∀ i, p.coeff i = q.coeff i

theorem isCanonical_empty [Zero R] : IsCanonical (mk (R := R) #[]) := sorry

theorem isCanonical_of_trim_eq [Zero R] [BEq R] [LawfulBEq R]
    {p : CPolynomial.Raw R} (hp : p.trim = p) :
    IsCanonical p := sorry

theorem isCanonical_trim [Zero R] [BEq R] [LawfulBEq R]
    (p : CPolynomial.Raw R) : IsCanonical p.trim := sorry

end Trim

end Foundations

end CPolynomial.Raw

end CompPoly
