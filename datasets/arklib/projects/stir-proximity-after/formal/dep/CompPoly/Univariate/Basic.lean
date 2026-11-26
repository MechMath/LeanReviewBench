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
public import dep.CompPoly.Univariate.Raw.Proofs

public section

namespace CompPoly

open CPolynomial.Raw

variable {R : Type*}

/-- Computable univariate polynomials are represented canonically with no trailing zeros.

  A polynomial `p : CPolynomial.Raw R` is canonical if its last stored coefficient is nonzero
  whenever the underlying array is nonempty. This gives an instance-stable carrier while keeping
  the raw normalization algorithms available separately.

  `Raw.mul` defers trimming to the end of its convolution fold (it accumulates with the
  untrimmed `Raw.mulRaw` and trims once). `Raw.powBySq` likewise routes through an
  untrimmed `powBySqUntrimmed` and trims once at the top of the repeated-squaring
  recursion. `CPolynomial.divX` skips trimming entirely: the input is canonical and
  `extract 1 size` only strips from the front, so the leading coefficient (when present)
  is preserved and the result is already canonical. The division wrappers (`divByMonic`,
  `modByMonic`, `modByMonicRemainderOnly`, `modByMonicByReversal`, `div`, `mod`) likewise
  skip the redundant post-trim: each underlying `Raw` algorithm bottoms out in operations
  (`Raw.add`, `Raw.sub`, `subScaledShift`) that already trim. `CLagrange.basis` folds the
  `s.erase i` factors with the untrimmed `Raw.mulRaw` via `Quotient.liftOn` on the
  underlying multiset and trims once at the end, and `CLagrange.interpolate` does the
  analogous deferred-trim sum via `Raw.addRaw`/`Raw.mulRaw`.
  Remaining opportunities to trim only at the end of an iterative computation:
  the `Array.foldl` accumulator in `Bivariate/ToPoly.lean` (`toPoly_foldl_zipIdx_eq_sum`),
  and the two `ExtTreeMap.foldl` monomial accumulators in `Multivariate/Operations.lean`.
  The NTT `butterflyStage` in `Univariate/NTT/Transform.lean` is not on this list: it
  operates on a scalar coefficient `Array R` and never calls `trim`.
-/
@[expose, implicit_reducible]
def CPolynomial (R : Type*) [Zero R] := { p : CPolynomial.Raw R // IsCanonical p }

namespace CPolynomial

section ZeroOnly

/-- Extensionality for canonical polynomials. -/
@[ext] theorem ext [Zero R] {p q : CPolynomial R} (h : p.val = q.val) : p = q := sorry

/-- Canonical polynomials coerce to raw polynomials. -/
instance [Zero R] : Coe (CPolynomial R) (CPolynomial.Raw R) where coe := Subtype.val

/-- The zero polynomial is canonical without any normalization assumptions. -/
instance [Zero R] : Zero (CPolynomial R) := ⟨⟨#[], Trim.isCanonical_empty⟩⟩

/-- The zero polynomial provides the inhabited instance. -/
instance [Zero R] : Inhabited (CPolynomial R) := ⟨0⟩

/-- `CPolynomial R` has `BEq` when `R` does, comparing the underlying coefficient arrays. -/
instance (R : Type*) [Zero R] [BEq R] : BEq (CPolynomial R) where
  beq p q := p.val == q.val

/-- `CPolynomial R` has `LawfulBEq` when `R` does: `p == q` iff `p = q`. -/
protected instance (R : Type*) [Zero R] [BEq R] [LawfulBEq R] : LawfulBEq (CPolynomial R) := sorry

/-- `CPolynomial R` has `DecidableEq` when `R` does, via the underlying `Array R` representation. -/
instance (R : Type*) [Zero R] [DecidableEq R] : DecidableEq (CPolynomial R) :=
  @Subtype.instDecidableEq
    (CPolynomial.Raw R)
    (fun p => IsCanonical p)
    inferInstance

end ZeroOnly

section Operations

/-- Canonical computable polynomials are trim-stable. -/
@[simp] theorem trim_eq [Zero R] [BEq R] [LawfulBEq R] (p : CPolynomial R) : p.val.trim = p.val := sorry

/-- Addition of canonical polynomials (result is canonical). -/
instance [Semiring R] [BEq R] [LawfulBEq R] : Add (CPolynomial R) where
  add p q := ⟨p.val + q.val,
    Trim.isCanonical_of_trim_eq (Raw.add_is_trimmed p.val q.val)⟩

protected theorem add_comm [Semiring R] [BEq R] [LawfulBEq R]
    (p q : CPolynomial R) : p + q = q + p := sorry

protected theorem add_assoc [Semiring R] [BEq R] [LawfulBEq R]
    (p q r : CPolynomial R) : p + q + r = p + (q + r) := sorry

protected theorem zero_add [Semiring R] [BEq R] [LawfulBEq R] (p : CPolynomial R) : 0 + p = p := sorry

protected theorem add_zero [Semiring R] [BEq R] [LawfulBEq R] (p : CPolynomial R) : p + 0 = p := sorry

/-- Scalar multiplication by a natural number (result is canonical). -/
def nsmul [Semiring R] [BEq R] [LawfulBEq R] (n : ℕ) (p : CPolynomial R) : CPolynomial R :=
  ⟨Raw.nsmul n p.val,
    Trim.isCanonical_of_trim_eq (sorry)⟩

protected theorem nsmul_zero [Semiring R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) : nsmul 0 p = 0 := sorry

theorem nsmul_succ [Semiring R] [BEq R] [LawfulBEq R]
    (n : ℕ) (p : CPolynomial R) : nsmul (n + 1) p = nsmul n p + p := sorry

instance [Semiring R] [BEq R] [LawfulBEq R] : AddCommSemigroup (CPolynomial R) where
  add_assoc := CPolynomial.add_assoc
  add_comm := CPolynomial.add_comm

/-- Multiplication of canonical polynomials.

  The product of two canonical polynomials is canonical because multiplication
  preserves the "no trailing zeros" property.
-/
instance [Semiring R] [BEq R] [LawfulBEq R] : Mul (CPolynomial R) where
  mul p q :=
    ⟨p.val * q.val, Trim.isCanonical_of_trim_eq (mul_is_trimmed p.val q.val)⟩

lemma one_is_trimmed [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] :
    (1 : CPolynomial.Raw R).trim = 1 := sorry

/-- The constant polynomial 1 is canonical, and is the Unit for multiplication.

  This is `#[1]`, which has no trailing zeros.

  This proof does not work without the assumption that R is non-trivial.
-/
instance [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] : One (CPolynomial R) where
  one := ⟨Raw.C 1, Trim.isCanonical_of_trim_eq one_is_trimmed⟩

instance [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] : Nontrivial (CPolynomial R) := sorry

/-- The coefficient of `X^i` in the polynomial. Returns `0` if `i` is out of bounds. -/
@[reducible]
def coeff [Zero R] (p : CPolynomial R) (i : ℕ) : R := p.val.coeff i

/-- Build a canonical polynomial from a dense coefficient array. -/
def ofArray [Zero R] [BEq R] [LawfulBEq R]
    (coeffs : Array R) : CPolynomial R :=
  let raw : CPolynomial.Raw R := coeffs
  ⟨raw.trim, Trim.isCanonical_trim raw⟩

/-- Construct a canonical polynomial from a coefficient function `Fin n → R`.

  Index `i` gives the coefficient of `X^i`; the resulting array is trimmed to remove
  trailing zeros. -/
def ofFn [Zero R] [BEq R] [LawfulBEq R] {n : ℕ} (f : Fin n → R) : CPolynomial R :=
  ofArray (Array.ofFn f)

/-- The constant polynomial `C r`. -/
def C [Zero R] [BEq R] [LawfulBEq R] (r : R) : CPolynomial R :=
  ⟨(Raw.C r).trim, Trim.isCanonical_trim (Raw.C r)⟩

/-- The variable `X`. -/
def X [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] : CPolynomial R :=
  ⟨Raw.X, Trim.isCanonical_of_trim_eq X_canonical⟩

/-- Construct a canonical monomial `c * X^n` as a `CPolynomial R`.

  The result is canonical (no trailing zeros) when `c ≠ 0`.
  For example, `monomial 2 3` represents `3 * X^2`.

  Note: If `c = 0`, this returns `0` (the zero polynomial).
-/
def monomial [Semiring R] [BEq R] [LawfulBEq R] [DecidableEq R]
    (n : ℕ) (c : R) : CPolynomial R :=
  ⟨Raw.monomial n c, Trim.isCanonical_of_trim_eq (Raw.monomial_canonical n c)⟩

/-- Return the degree of a `CPolynomial`. -/
def degree [Zero R] (p : CPolynomial R) : WithBot ℕ :=
  match p.val.size with
  | 0 => ⊥
  | .succ n => n

/-- Natural number degree of a canonical polynomial.

  Returns the degree as a natural number. For the zero polynomial, returns `0`.
  This matches Mathlib's `Polynomial.natDegree` API.
-/
def natDegree [Zero R] (p : CPolynomial R) : ℕ :=
  match p.val.size with
  | 0 => 0
  | .succ n => n

/-- Return the leading coefficient of a `CPolynomial` as the last coefficient
of the trimmed array, or `0` if the trimmed array is empty. -/
def leadingCoeff [Zero R] (p : CPolynomial R) : R := p.val.getLastD 0

/-- Evaluate a polynomial at a point. -/
def eval [Semiring R] (x : R) (p : CPolynomial R) : R :=
  p.val.zipIdx.foldl (fun acc ⟨a, i⟩ => acc + a * x ^ i) 0

/-- Evaluate at `x : S` via a ring hom
`f : R →+* S`; `eval₂ f x p = f(a₀) + f(a₁)*x + f(a₂)*x² + ...`. -/
def eval₂ {S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (x : S) (p : CPolynomial R) : S :=
  p.val.zipIdx.foldl (fun acc ⟨a, i⟩ => acc + f a * x ^ i) 0

/-- Evaluate at `x : S` via a ring hom using Horner's method. -/
@[inline, specialize]
def eval₂Horner {S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (x : S) (p : CPolynomial R) : S :=
  p.val.eval₂Horner f x

/-- Evaluate a polynomial at a point using Horner's method. -/
@[inline, specialize]
def evalHorner [Semiring R] (x : R) (p : CPolynomial R) : R :=
  p.eval₂Horner (RingHom.id R) x

/-- Compiled code evaluates by Horner's method; `eval₂` remains the specification. -/
@[csimp]
theorem eval₂_eq_eval₂Horner : @eval₂ = @eval₂Horner := sorry

/-- Compiled code evaluates by Horner's method; `eval` remains the specification. -/
@[csimp]
theorem eval_eq_evalHorner : @eval = @evalHorner := sorry

/-- The support of a polynomial: indices with nonzero coefficients. -/
def support [Zero R] [BEq R] (p : CPolynomial R) : Finset ℕ :=
  (Finset.range p.val.size).filter (fun i => p.val.coeff i != 0)

/-- Number of coefficients (length of the underlying array). -/
def size [Zero R] (p : CPolynomial R) : ℕ := p.val.size

/-- Upper bound on degree: `size - 1` if non-empty, `⊥` if empty. -/
def degreeBound [Zero R] (p : CPolynomial R) : WithBot Nat := p.degree

/-- An index is in the support iff the coefficient there is nonzero. -/
lemma mem_support_iff [Zero R] [BEq R] [LawfulBEq R] (p : CPolynomial R) (i : ℕ) :
    i ∈ p.support ↔ coeff p i ≠ 0 := sorry

theorem natDegree_zero [Zero R] [BEq R] [LawfulBEq R] :
    (0 : CPolynomial R).natDegree = 0 := sorry

section Division

/-- Quotient of `p` by `q` (when `R` is a field). -/
def div [Field R] [BEq R] [LawfulBEq R] (p q : CPolynomial R) : CPolynomial R :=
  ⟨Raw.div p.val q.val, Trim.isCanonical_of_trim_eq (Raw.div_canonical p.val q.val)⟩

/-- Remainder of `p` modulo `q` (when `R` is a field). -/
def mod [Field R] [BEq R] [LawfulBEq R] (p q : CPolynomial R) : CPolynomial R :=
  ⟨Raw.mod p.val q.val, Trim.isCanonical_of_trim_eq (Raw.mod_canonical p.val q.val)⟩

instance [Field R] [BEq R] [LawfulBEq R] : Div (CPolynomial R) := ⟨div⟩

instance [Field R] [BEq R] [LawfulBEq R] : Mod (CPolynomial R) := ⟨mod⟩

end Division

end Operations

section Semiring

protected lemma one_mul [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p : CPolynomial R) : 1 * p = p := sorry

protected lemma mul_one [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p : CPolynomial R) : p * 1 = p := sorry

protected lemma mul_assoc [Semiring R] [BEq R] [LawfulBEq R]
    (p q r : CPolynomial R) : (p * q) * r = p * (q * r) := sorry

lemma zero_mul [Semiring R] [BEq R] [LawfulBEq R] (p : CPolynomial R) : 0 * p = 0 := sorry

lemma mul_zero [Semiring R] [BEq R] [LawfulBEq R] (p : CPolynomial R) : p * 0 = 0 := sorry

/--
`CPolynomial R` forms a commutative monoid when `R` is a semiring.
-/
instance [Semiring R] [BEq R] [LawfulBEq R] : AddCommMonoid (CPolynomial R) where
  zero := 0
  add := (· + ·)
  add_assoc := CPolynomial.add_assoc
  add_comm := CPolynomial.add_comm
  zero_add := CPolynomial.zero_add
  add_zero := sorry
  nsmul := CPolynomial.nsmul
  nsmul_zero := CPolynomial.nsmul_zero
  nsmul_succ := CPolynomial.nsmul_succ

/-- `CPolynomial R` forms a semiring when `R` is a semiring.

  The semiring structure extends the `AddCommGroup` structure with multiplication.
  All operations preserve the canonical property (no trailing zeros).
-/
instance [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] : Semiring (CPolynomial R) where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  add_assoc := CPolynomial.add_assoc
  zero_add := CPolynomial.zero_add
  add_zero := sorry
  add_comm := CPolynomial.add_comm
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  left_distrib := sorry
  right_distrib := sorry
  nsmul := CPolynomial.nsmul
  nsmul_zero := CPolynomial.nsmul_zero
  nsmul_succ := CPolynomial.nsmul_succ
  npow n p := ⟨Raw.powBySq p.val n, sorry⟩
  npow_zero := sorry
  npow_succ := sorry
  natCast_zero := sorry
  natCast_succ := sorry

end Semiring

section CommSemiring

protected lemma mul_comm [CommSemiring R] [BEq R] [LawfulBEq R]
    (p q : CPolynomial R) : p * q = q * p := sorry

/-- `CPolynomial R` forms a commutative semiring when `R` is a commutative semiring.

  Commutativity follows from the commutativity of multiplication in the base ring.
-/
instance [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] : CommSemiring (CPolynomial R) where
  __ := (inferInstance : Semiring (CPolynomial R))
  mul_comm := sorry

end CommSemiring

section Ring

instance [Ring R] [BEq R] [LawfulBEq R] : Neg (CPolynomial R) where
  neg p := ⟨-p.val, Trim.isCanonical_of_trim_eq (neg_trim p.val (trim_eq p))⟩

instance [Ring R] [BEq R] [LawfulBEq R] : Sub (CPolynomial R) where
  sub p q := p + -q

protected theorem neg_add_cancel [Ring R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) : -p + p = 0 := sorry

instance [Ring R] [BEq R] [LawfulBEq R] : AddCommGroup (CPolynomial R) where
  zero := 0
  add := (· + ·)
  neg := Neg.neg
  sub := HSub.hSub
  add_assoc := CPolynomial.add_assoc
  zero_add := CPolynomial.zero_add
  add_zero := CPolynomial.add_zero
  add_comm := CPolynomial.add_comm
  neg_add_cancel := sorry
  nsmul := CPolynomial.nsmul
  nsmul_zero := CPolynomial.nsmul_zero
  nsmul_succ := CPolynomial.nsmul_succ
  sub_eq_add_neg := sorry
  zsmul := zsmulRec
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry

/-- `CPolynomial R` forms a ring when `R` is a ring.

  The ring structure extends the semiring structure with negation and subtraction.
  Most of the structure is already provided by the `Semiring` instance.
-/
instance [Ring R] [BEq R] [LawfulBEq R] [Nontrivial R] : Ring (CPolynomial R) where
  __ := (inferInstance : Semiring (CPolynomial R))
  __ := (inferInstance : AddCommGroup (CPolynomial R))
  intCast_ofNat := sorry
  intCast_negSucc := sorry

end Ring

section CommRing

/-- `CPolynomial R` forms a commutative ring when `R` is a commutative ring.

  This combines the `CommSemiring` and `Ring` structures.
-/
instance [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] : CommRing (CPolynomial R) where
  __ := (inferInstance : Ring (CPolynomial R))
  __ := (inferInstance : CommSemiring (CPolynomial R))

end CommRing

section Module

/-- Scalar multiplication for canonical polynomials: multiply each coefficient by `r`,
then trim to restore canonicity. -/
instance smul [Semiring R] [BEq R] [LawfulBEq R] : SMul R (CPolynomial R) where
  smul r p := ⟨(Raw.smul r p.val).trim, Trim.isCanonical_trim (Raw.smul r p.val)⟩

/-- Scalar multiplication on 0 gives 0. -/
protected lemma smul_zero [Semiring R] [BEq R] [LawfulBEq R]
    (r : R) : r • (0 : CPolynomial R) = 0 := sorry

/-- Scalar multiplication distributes. -/
protected lemma smul_add [Semiring R] [BEq R] [LawfulBEq R]
    (r : R) (p q : CPolynomial R) :
    r • (p + q) = r • p + r • q := sorry

/-- Scalar multiplication distributes across scalar addition. -/
protected lemma add_smul [Semiring R] [BEq R] [LawfulBEq R]
    (r s : R) (p : CPolynomial R) :
    (r + s) • p = r • p + s • p := sorry

/-- Scalar multiplication by 0 gives 0. -/
protected lemma zero_smul [Semiring R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) : (0 : R) • p = 0 := sorry

/-- Scalar multiplication on p by 1 gives p. -/
protected lemma one_smul [Semiring R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) : (1 : R) • p = p := sorry

/-- Scalar multiplication is associative. -/
lemma mul_smul [Semiring R] [BEq R] [LawfulBEq R]
    (r s : R) (p : CPolynomial R) :
    (r * s) • p = r • (s • p) := sorry

/-- `CPolynomial` forms a module when R is a semiring. -/
instance [Semiring R] [BEq R] [LawfulBEq R] : Module R (CPolynomial R) where
  smul:= SMul.smul
  mul_smul := mul_smul
  one_smul := CPolynomial.one_smul
  smul_zero := CPolynomial.smul_zero
  smul_add := CPolynomial.smul_add
  add_smul := CPolynomial.add_smul
  zero_smul := CPolynomial.zero_smul

end Module

end CPolynomial

end CompPoly
