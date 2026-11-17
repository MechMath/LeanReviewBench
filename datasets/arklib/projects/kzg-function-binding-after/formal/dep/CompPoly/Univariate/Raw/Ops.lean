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

public section

namespace CompPoly

namespace CPolynomial.Raw

variable {R : Type*}

variable {Q : Type*}

section Operations

section Semiring

variable {S : Type*}

/-- Evaluates a `CPolynomial.Raw` at `x : S` using a ring homomorphism `f : R →+* S`.

  Computes `f(a₀) + f(a₁) * x + f(a₂) * x² + ...` where `aᵢ` are the coefficients.  -/
def eval₂ [Semiring R] [Semiring S] (f : R →+* S) (x : S) (p : CPolynomial.Raw R) : S :=
  p.zipIdx.foldl (fun acc ⟨a, i⟩ => acc + f a * x ^ i) 0

/-- Evaluates a `CPolynomial.Raw` at `x : S` using Horner's method.

  Computes `f(aₙ) + x * (f(aₙ₋₁) + x * (... + x * f(a₀)))` via a right fold. -/
@[inline, specialize]
def eval₂Horner [Semiring R] [Semiring S] (f : R →+* S) (x : S) (p : CPolynomial.Raw R) : S :=
  p.foldr (fun a acc => acc * x + f a) 0

/-- Evaluates a `CPolynomial.Raw` at a given value -/
@[inline, specialize]
def eval [Semiring R] (x : R) (p : CPolynomial.Raw R) : R :=
  p.eval₂ (RingHom.id R) x

/-- Evaluates a `CPolynomial.Raw` at a given value using Horner's method. -/
@[inline, specialize]
def evalHorner [Semiring R] (x : R) (p : CPolynomial.Raw R) : R :=
  p.eval₂Horner (RingHom.id R) x

/-- Raw addition: pointwise sum of coefficient arrays (padded to equal length).

  The result may have trailing zeros and should be trimmed for canonical form. -/
@[inline, specialize]
def addRaw [Zero R] [Add R] (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  let ⟨p', q'⟩ := Array.matchSize p q 0
  .mk (Array.zipWith (· + ·) p' q' )

/-- Addition of two `CPolynomial.Raw`s, with result trimmed. -/
@[inline, specialize]
def add [Zero R] [Add R] [BEq R] (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  addRaw p q |> trim

section SMulDefs

/-- Scalar multiplication: multiplies each coefficient by `r`. -/
@[inline, specialize]
def smul [Mul R] (r : R) (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  .mk (Array.map (fun a => r * a) p)

/-- Raw scalar multiplication by a natural number (may have trailing zeros). -/
@[inline, specialize]
def nsmulRaw [Semiring R] (n : ℕ) (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  .mk (Array.map (fun a => n * a) p)

/-- Scalar multiplication of `CPolynomial.Raw` by a natural number, with result trimmed. -/
@[inline, specialize]
def nsmul [Semiring R] [BEq R] (n : ℕ) (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  nsmulRaw n p |> trim

end SMulDefs

section MulPowXDefs

/-- Multiplication by `X^i`: shifts coefficients right by `i` positions (prepends `i` zeros). -/
@[inline, specialize]
def mulPowX [Zero R] (i : Nat) (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  .mk (Array.replicate i 0 ++ p)

end MulPowXDefs

/-- Multiplication accumulator using the naive `O(n²)` algorithm: `Σᵢ (aᵢ * q) * X^i`.

  The partial sums are combined with the untrimmed `addRaw`, so the result may carry
  trailing zeros and should be trimmed for canonical form. Deferring the trim to the
  end (see `mul`) avoids an `O(size)` scan after every partial sum. -/
@[inline, specialize]
def mulRaw [Semiring R] (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  p.zipIdx.foldl (fun acc ⟨a, i⟩ => acc.addRaw <| (smul a q).mulPowX i) (mk #[])

/-- Multiplication using the naive `O(n²)` algorithm: `Σᵢ (aᵢ * q) * X^i`.

  Trims only once, at the end of the convolution fold, rather than after every
  partial sum (`mulRaw` does the untrimmed accumulation). -/
@[inline, specialize]
def mul [Semiring R] [BEq R] (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  (mulRaw p q).trim

/-- Exponentiation of a `CPolynomial.Raw` by a natural number `n` via repeated multiplication.
This is the specification; `powBySq` is the efficient O(log n) implementation. -/
@[inline, specialize]
def pow [Semiring R] [BEq R] (p : CPolynomial.Raw R) (n : Nat) : CPolynomial.Raw R :=
  (mul p)^[n] (C 1)

/-- Repeated-squaring core that accumulates with the untrimmed `mulRaw`, deferring
the canonicalization trim to the outer `powBySq` wrapper. The output may carry
trailing zeros and is not in canonical form.

For $ n > 0 $, computes $ p ^ n $ by recursing on $ n / 2 $:
* If $ n $ is even: $ (p ^ {n/2})^2 $
* If $ n $ is odd:  $ p \cdot (p ^ {n/2})^2 $
-/
@[inline, specialize]
def powBySqUntrimmed [Semiring R] (p : CPolynomial.Raw R) : Nat → CPolynomial.Raw R
  | 0 => C 1
  | n + 1 =>
    let half := powBySqUntrimmed p ((n + 1) / 2)
    let sq := mulRaw half half
    if (n + 1) % 2 = 0 then sq else mulRaw p sq
  decreasing_by omega

/-- Exponentiation via repeated squaring: $ O(\log n) $ multiplications
instead of $ O(n) $. Delegates to `powBySqUntrimmed` and trims only once
at the end, rather than after every squaring step.
-/
@[inline, specialize]
def powBySq [Semiring R] [BEq R] (p : CPolynomial.Raw R) (n : Nat) : CPolynomial.Raw R :=
  (powBySqUntrimmed p n).trim

instance : Zero (CPolynomial.Raw R) := ⟨#[]⟩

instance [One R] : One (CPolynomial.Raw R) := ⟨C 1⟩

instance [Zero R] [Add R] [BEq R] : Add (CPolynomial.Raw R) := ⟨add⟩

instance [Mul R] : SMul R (CPolynomial.Raw R) := ⟨smul⟩

instance [Semiring R] [BEq R] : SMul ℕ (CPolynomial.Raw R) := ⟨nsmul⟩

instance [Semiring R] [BEq R] : Mul (CPolynomial.Raw R) := ⟨mul⟩

instance [Semiring R] [BEq R] : Pow (CPolynomial.Raw R) Nat := ⟨pow⟩

instance [NatCast R] : NatCast (CPolynomial.Raw R) := ⟨fun n => C (n : R)⟩

/-- Backend for computing the low `k` coefficients of a raw product. -/
structure MulLowContext (R : Type*) [Semiring R] [BEq R] [LawfulBEq R] where
  /-- Return the low `k` coefficients of `p * q`. -/
  mulLow : Nat → CPolynomial.Raw R → CPolynomial.Raw R → CPolynomial.Raw R
  /-- The backend does not return coefficients at degree `>= k`. -/
  size_le : ∀ k p q, (mulLow k p q).size ≤ k
  /-- Low coefficients agree with ordinary raw multiplication. -/
  coeff_of_lt : ∀ k p q i, i < k → (mulLow k p q).coeff i = (p * q).coeff i

/-- Upper bound on degree: `size - 1` if non-empty, `⊥` if empty. -/
def degreeBound (p : CPolynomial.Raw R) : WithBot Nat :=
  match p.size with
  | 0 => ⊥
  | .succ n => n

end Semiring

section Ring

/-- Negation of a `CPolynomial.Raw`. -/
@[inline, specialize]
def neg [Neg R] (p : CPolynomial.Raw R) : CPolynomial.Raw R := p.map (fun a => -a)

/-- Subtraction of two `CPolynomial.Raw`s. -/
@[inline, specialize]
def sub [Zero R] [Add R] [Neg R] [BEq R]
    (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  p.add q.neg

instance [Neg R] : Neg (CPolynomial.Raw R) := ⟨neg⟩

instance [Zero R] [Add R] [Neg R] [BEq R] : Sub (CPolynomial.Raw R) := ⟨sub⟩

instance [IntCast R] : IntCast (CPolynomial.Raw R) := ⟨fun n => C (n : R)⟩

end Ring

end Operations

end CPolynomial.Raw

end CompPoly
