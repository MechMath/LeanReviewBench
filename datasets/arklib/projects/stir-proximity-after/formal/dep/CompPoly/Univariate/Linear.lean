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

public section

namespace CompPoly

namespace CPolynomial

variable {R : Type*}

section LinearMaps

variable [Semiring R] [BEq R] [LawfulBEq R]

end LinearMaps

section DegreeBounds

variable [Zero R]

/-- The set of `CPolynomial R` consisting of polynomials of degree < `n`. -/
def degreeLT (n : ℕ) : Set (CPolynomial R) :=
  { p | p.val.degreeBound < n }

/-- Membership in `degreeLT` is the corresponding strict degree bound. -/
theorem mem_degreeLT {n : ℕ} {p : CPolynomial R} :
    p ∈ degreeLT (R := R) n ↔ p.degree < n := sorry

/-- The zero polynomial has bounded degree for every cutoff. -/
theorem zero_mem_degreeLT (n : ℕ) : (0 : CPolynomial R) ∈ degreeLT (R := R) n := sorry

end DegreeBounds

section DegreeLTSubtype

variable [Semiring R] [BEq R] [LawfulBEq R]

/-- `degreeLT n` is closed under addition. -/
theorem add_mem_degreeLT {n : ℕ} {p q : CPolynomial R}
    (hp : p ∈ degreeLT (R := R) n) (hq : q ∈ degreeLT (R := R) n) :
    p + q ∈ degreeLT (R := R) n := sorry

/-- `degreeLT n` is closed under additive scalar multiplication. -/
theorem nsmul_mem_degreeLT {n m : ℕ} {p : CPolynomial R}
    (hp : p ∈ degreeLT (R := R) n) :
    m • p ∈ degreeLT (R := R) n := sorry

/-- `degreeLT n` is closed under semiring scalar multiplication. -/
theorem smul_mem_degreeLT {n : ℕ} (r : R) {p : CPolynomial R}
    (hp : p ∈ degreeLT (R := R) n) :
    r • p ∈ degreeLT (R := R) n := sorry

instance (n : ℕ) : Zero ↥(degreeLT (R := R) n) where
  zero := ⟨0, zero_mem_degreeLT (R := R) n⟩

instance (n : ℕ) : Add ↥(degreeLT (R := R) n) where
  add p q := ⟨p.1 + q.1, add_mem_degreeLT p.2 q.2⟩

instance (n : ℕ) : SMul ℕ ↥(degreeLT (R := R) n) where
  smul m p := ⟨m • p.1, nsmul_mem_degreeLT (R := R) (n := n) (m := m) p.2⟩

instance (n : ℕ) : SMul R ↥(degreeLT (R := R) n) where
  smul r p := ⟨r • p.1, smul_mem_degreeLT (R := R) (n := n) r p.2⟩

instance (n : ℕ) : AddCommMonoid ↥(degreeLT (R := R) n) where
  add_assoc := sorry
  add_comm := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := (· • ·)
  nsmul_zero := sorry
  nsmul_succ := sorry

instance (n : ℕ) : Module R ↥(degreeLT (R := R) n) where
  smul := (· • ·)
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

end DegreeLTSubtype

end CPolynomial

end CompPoly
