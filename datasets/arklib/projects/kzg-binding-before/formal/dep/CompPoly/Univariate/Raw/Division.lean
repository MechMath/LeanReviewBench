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
public import dep.CompPoly.Univariate.Raw.Ops

public section

namespace CompPoly

namespace CPolynomial.Raw

variable {R : Type*}

section Division

variable [BEq R]

/-- Division with remainder by a monic polynomial using polynomial long division. -/
@[expose]
def divModByMonicAux [CommRing R] (p : CPolynomial.Raw R) (q : CPolynomial.Raw R) :
    CPolynomial.Raw R × CPolynomial.Raw R :=
  go p.size p q
where
  go : Nat → CPolynomial.Raw R → CPolynomial.Raw R → CPolynomial.Raw R × CPolynomial.Raw R
  | 0, p, _ => ⟨0, p⟩
  | n+1, p, q =>
      if p.size < q.size then
        ⟨0, p⟩
      else
        let k := p.size - q.size
        let q' := C p.leadingCoeff * (q * X.pow k)
        let p' := (p - q').trim
        let (e, f) := go n p' q
        ⟨e + C p.leadingCoeff * X^k, f⟩

/-- Division of `p : CPolynomial.Raw R` by a monic `q : CPolynomial.Raw R`. -/
def divByMonic [CommRing R] (p : CPolynomial.Raw R) (q : CPolynomial.Raw R) :
    CPolynomial.Raw R :=
  (divModByMonicAux p q).1

/-- Modulus of `p : CPolynomial.Raw R` by a monic `q : CPolynomial.Raw R`. -/
def modByMonic [CommRing R] (p : CPolynomial.Raw R) (q : CPolynomial.Raw R) :
    CPolynomial.Raw R :=
  (divModByMonicAux p q).2

/-- Division of two `CPolynomial.Raw`s. -/
def div [Field R] (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  (C (q.leadingCoeff)⁻¹ • p).divByMonic (C (q.leadingCoeff)⁻¹ * q)

/-- Modulus of two `CPolynomial.Raw`s. -/
def mod [Field R] (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  (C (q.leadingCoeff)⁻¹ • p).modByMonic (C (q.leadingCoeff)⁻¹ * q)

instance [Field R] : Div (CPolynomial.Raw R) := ⟨div⟩

instance [Field R] : Mod (CPolynomial.Raw R) := ⟨mod⟩

end Division

end CPolynomial.Raw

end CompPoly
