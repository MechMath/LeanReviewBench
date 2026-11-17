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
public import dep.CompPoly.Univariate.Basic
public import dep.CompPoly.Univariate.Raw.Core
public import dep.CompPoly.Univariate.Raw.Division
public import dep.CompPoly.Univariate.Raw.Ops
public import dep.CompPoly.Univariate.Raw.Proofs

@[expose] public section

namespace CompPoly

/-- Computable bivariate polynomials: `F[X][Y]` as `CPolynomial (CPolynomial R)`.

  Each `p : CBivariate R` is a polynomial in `Y` whose coefficients are univariate polynomials
  in `X`. The outer structure is indexed by powers of `Y`, the inner by powers of `X`.
  -/
@[implicit_reducible]
def CBivariate (R : Type*) [Zero R] :=
    CPolynomial (CPolynomial R)

namespace CBivariate

section ZeroOnly

variable {R : Type*} [Zero R]

/-- Extensionality: two bivariate polynomials are equal if their underlying values are. -/
@[ext] theorem ext {p q : CBivariate R} (h : p.val = q.val) : p = q := sorry

/-- Coerce to the underlying univariate polynomial (in Y) with polynomial coefficients. -/
instance : Coe (CBivariate R) (CPolynomial (CPolynomial R)) where coe := id

/-- The zero bivariate polynomial is canonical. -/
instance : Inhabited (CBivariate R) := inferInstanceAs (Inhabited (CPolynomial (CPolynomial R)))

instance [BEq R] : BEq (CBivariate R) :=
  inferInstanceAs (BEq (CPolynomial (CPolynomial R)))

instance [BEq R] [LawfulBEq R] : LawfulBEq (CBivariate R) := sorry

instance [DecidableEq R] : DecidableEq (CBivariate R) :=
  inferInstanceAs (DecidableEq (CPolynomial (CPolynomial R)))

end ZeroOnly

section Semiring

variable {R : Type*}

variable [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]

/-- Additive structure on CBivariate R -/
instance : AddCommMonoid (CBivariate R) :=
  inferInstanceAs (AddCommMonoid (CPolynomial (CPolynomial R)))

/-- Ring structure on CBivariate R (for ring equiv with Mathlib in ToPoly). -/
instance : Semiring (CBivariate R) :=
  inferInstanceAs (Semiring (CPolynomial (CPolynomial R)))

end Semiring

section CommSemiring

variable {R : Type*}

variable [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]

instance : CommSemiring (CBivariate R) :=
  inferInstanceAs (CommSemiring (CPolynomial (CPolynomial R)))

end CommSemiring

section Ring

variable {R : Type*}

variable [Ring R] [BEq R] [LawfulBEq R] [Nontrivial R]

instance : Ring (CBivariate R) :=
  inferInstanceAs (Ring (CPolynomial (CPolynomial R)))

end Ring

section CommRing

variable {R : Type*}

variable [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]

instance : CommRing (CBivariate R) :=
  inferInstanceAs (CommRing (CPolynomial (CPolynomial R)))

end CommRing

section Operations

/-- The variable X (inner variable). As bivariate: polynomial in Y with single coeff `X` at Y^0. -/
def X {R : Type*} [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] : CBivariate R :=
  CPolynomial.C CPolynomial.X

/-- The variable Y (outer variable). Monomial `Y^1` with coefficient 1. -/
def Y {R : Type*} [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R] :
    CBivariate R :=
  CPolynomial.monomial 1 (CPolynomial.C 1)

/-- Coefficient of `X^i Y^j` in the bivariate polynomial. Here `i` is the X-exponent (inner)
    and `j` is the Y-exponent (outer). ArkLib: `Polynomial.Bivariate.coeff f i j`. -/
def coeff {R : Type*} [Zero R] (f : CBivariate R) (i j : ℕ) : R :=
  (f.val.coeff j).coeff i

end Operations

section CoeffLemmas

variable {R : Type*}

end CoeffLemmas

section WeightedDegreeLemmas

variable {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Semiring R]

end WeightedDegreeLemmas

end CBivariate

end CompPoly
