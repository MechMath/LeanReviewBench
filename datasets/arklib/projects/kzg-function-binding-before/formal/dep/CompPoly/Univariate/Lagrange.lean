module

public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.Algebra.Tropical.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Nat.Log
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Order.Lattice.Nat
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Tactic.Cases
public import dep.CompPoly.Data.Array.Lemmas
public import dep.CompPoly.Univariate.Basic
public import dep.CompPoly.Univariate.Linear
public import dep.CompPoly.Univariate.Raw.Core
public import dep.CompPoly.Univariate.Raw.Division
public import dep.CompPoly.Univariate.Raw.Ops
public import dep.CompPoly.Univariate.Raw.Proofs
public import dep.CompPoly.Univariate.ToPoly.Core

@[expose] public section

namespace CompPoly

namespace CPolynomial

namespace CLagrange

variable {R : Type*} [BEq R] [Field R] [LawfulBEq R]

/-- `basisDivisor xᵢ xⱼ` is the unique linear or constant computable polynomial such that
when evaluated at `xᵢ` it gives `1` and `xⱼ` it gives `0` (where when `xᵢ = xⱼ` it is
identically `0`). Such polynomials are the building blocks for the Lagrange interpolants. -/
def basisDivisor (xᵢ xⱼ : R) : CPolynomial R :=
  C (xᵢ - xⱼ)⁻¹ * (X - C xⱼ)

/-- `basisDivisor`-product fold over a list, combining factors with the untrimmed
`Raw.mulRaw`. The wrapping `basis` definition trims this once. -/
def basisListRaw {ι : Type*} (x : ι → R) (i : ι) (l : List ι) :
    CPolynomial.Raw R :=
  l.foldr (fun j acc => Raw.mulRaw (basisDivisor (x i) (x j)).val acc) (Raw.C 1)

lemma basisListRaw_trim_perm {ι : Type*} (x : ι → R) (i : ι)
    {l₁ l₂ : List ι} (h : l₁.Perm l₂) :
    (basisListRaw x i l₁).trim = (basisListRaw x i l₂).trim := sorry

/-- Computable Lagrange basis polynomials indexed by `s : Finset ι`, defined at nodes `x i` for a
map `x : ι → F`. For `i, j ∈ s`, `basis s x i` evaluates to `0` at `x j` for `i ≠ j`. When
`x` is injective on `s`, `basis s x i` evaluates to 1 at `x i`.

The product folds `(s.erase i).val` with the untrimmed `Raw.mulRaw` via `Quotient.liftOn`
and trims once at the end, rather than paying one `Raw.mul` trim per factor (as the
`Finset.prod` formulation would). -/
def basis {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → R) (i : ι) :
    CPolynomial R :=
  Quotient.liftOn (s.erase i).val
    (fun l => ⟨(basisListRaw x i l).trim, Raw.Trim.isCanonical_trim _⟩)
    (fun _ _ h => Subtype.ext (basisListRaw_trim_perm x i h))

def interpolateListRaw {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → R) (y : ι → R) (l : List ι) : CPolynomial.Raw R :=
  l.foldr
    (fun i acc => Raw.addRaw (Raw.mulRaw (Raw.C (y i)) (basis s x i).val) acc)
    (Raw.mk #[])

lemma interpolateListRaw_trim_perm {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → R) (y : ι → R) {l₁ l₂ : List ι} (h : l₁.Perm l₂) :
    (interpolateListRaw s x y l₁).trim = (interpolateListRaw s x y l₂).trim := sorry

/-- Computable raw-fold form of the interpolation polynomial: defer trimming to the
end of the `Finset.sum`. -/
def interpolateRaw {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → R) (y : ι → R) : CPolynomial R :=
  Quotient.liftOn s.val
    (fun l => ⟨(interpolateListRaw s x y l).trim, Raw.Trim.isCanonical_trim _⟩)
    (fun _ _ h => Subtype.ext (interpolateListRaw_trim_perm s x y h))

/-- Computable Lagrange interpolation: given a finset `s : Finset ι`, a nodal map `x : ι → F`
injective on `s` and a value function `y : ι → F`, `interpolate s x y` is the unique computable
polynomial of degree `< #s` that takes value `y i` on `x i` for all `i` in `s`. -/
def interpolate {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → R) :
    (ι → R) →ₗ[R] CPolynomial R where
    toFun := fun y ↦ interpolateRaw s x y
    map_add' := sorry
    map_smul' := sorry

end CLagrange

end CPolynomial

end CompPoly
