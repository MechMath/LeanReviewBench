module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic

@[expose] public section

namespace RestrictedProduct

variable {ι : Type*}

variable {R : ι → Type*} {A : (i : ι) → Set (R i)}

variable {ℱ : Filter ι}

variable {S : ι → Type*}

variable [Π i, SetLike (S i) (R i)]

variable {B : Π i, S i}

variable
    {G H : ι → Type*}
    {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)}

end RestrictedProduct

open RestrictedProduct

section modules

variable {ι₁ ι₂ : Type*}

variable (R₁ : ι₁ → Type*) (R₂ : ι₂ → Type*)

variable {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}

variable {A₁ : (i : ι₁) → Set (R₁ i)} {A₂ : (i : ι₂) → Set (R₂ i)}

variable {S₁ : ι₁ → Type*} {S₂ : ι₂ → Type*}

variable [Π i, SetLike (S₁ i) (R₁ i)] [Π j, SetLike (S₂ j) (R₂ j)]

variable {B₁ : Π i, S₁ i} {B₂ : Π j, S₂ j}

variable (f : ι₂ → ι₁) (hf : Filter.Tendsto f 𝓕₂ 𝓕₁)

variable {A : Type*} [Semiring A]

variable [Π i, AddCommMonoid (R₁ i)] [Π i, AddCommMonoid (R₂ i)] [Π i, Module A (R₁ i)]
    [Π i, Module A (R₂ i)] [∀ i, AddSubmonoidClass (S₁ i) (R₁ i)]
    [∀ i, AddSubmonoidClass (S₂ i) (R₂ i)] [∀ i, SMulMemClass (S₁ i) A (R₁ i)]
    [∀ i, SMulMemClass (S₂ i) A (R₂ i)]
    (φ : ∀ j, R₁ (f j) →ₗ[A] R₂ j)
    (hφ : ∀ᶠ j in 𝓕₂, Set.MapsTo (φ j) (B₁ (f j)) (B₂ j))

/--
Given two restricted products `Πʳ (i : ι₁), [R₁ i, B₁ i]_[𝓕₁]` and `Πʳ (j : ι₂), [R₂ j, B₂ j]_[𝓕₂]`
of `A`-modules, `RestrictedProduct.mapAlongLinearMap` gives an `A`-linear map between them.
The data needed is a function `f : ι₂ → ι₁` such that `𝓕₂` tends to `𝓕₁` along `f`, and `A`-linear
maps `φ j : R₁ (f j) → R₂ j` sending `B₁ (f j)` into `B₂ j` for an `𝓕₂`-large set of `j`'s.
-/
def RestrictedProduct.mapAlongLinearMap :
    Πʳ i, [R₁ i, B₁ i]_[𝓕₁] →ₗ[A] Πʳ j, [R₂ j, B₂ j]_[𝓕₂] where
  __ := mapAlongAddMonoidHom R₁ R₂ f hf (fun j ↦ φ j) hφ
  map_smul' a f := sorry

variable (A : Type*) [CommRing A] {ι : Type*} (R : ι → Type*)
  [Π i, AddCommGroup (R i)] [∀ i, Module A (R i)] (C : ∀ i, Submodule A (R i))

/-- A linear map version of `RestrictedProduct.inclusion` :
if `𝓕 ≤ 𝓖` then there's a linear map
`Πʳ i, [R i, C i]_[𝓖] →ₗ[A] Πʳ i, [R i, C i]_[𝓕]` where the `R i`
are `A`-modules and the `C i` are submodules.
-/
def RestrictedProduct.inclusionLinearMap
     {𝓕 𝓖 : Filter ι} (h : 𝓕 ≤ 𝓖) :
    Πʳ i, [R i, C i]_[𝓖] →ₗ[A] Πʳ i, [R i, C i]_[𝓕] :=
  mapAlongLinearMap R R id h (fun _ ↦ .id)
  (Filter.Eventually.of_forall <| fun _ _ ↦ id)

end modules

variable {ι : Type*}

variable {ℱ : Filter ι}
    {G H : ι → Type*}
    {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)}

namespace RestrictedProduct

section supports

variable {S T : ι → Type*}

variable [Π i, SetLike (S i) (G i)] [Π i, SetLike (T i) (H i)]

variable {A : Π i, S i} {B : Π i, T i}

end supports

section components

variable {ι₂ : Type*} {f : ι₂ → ι} {𝒢 : Filter ι₂}

variable {G₂ : ι₂ → Type*} {C₂ : (i : ι₂) → Set (G₂ i)}

variable (hf : 𝒢 = Filter.comap f ℱ)

variable (φ : Πʳ i, [G i, C i]_[ℱ] → Πʳ i, [G₂ i, C₂ i]_[𝒢])

variable (g : (j : ι₂) → G (f j) → G₂ j) (hcomponent : ∀ x j, φ x j = g j (x (f j)))

variable [∀ j, Nonempty (C₂ j)]

end components

section structure_map

/-- The structure map for a restricted product of ring. -/
def structureMapRingHom {ι : Type*} (M : ι → Type*) [(i : ι) → Ring (M i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (M i)] [∀ i, SubringClass (S i) (M i)] (A : Π i, S i)
    (𝓕 : Filter ι) : ((i : ι) → (A i)) →+* Πʳ (i : ι), [M i, Subring.ofClass (A i)]_[𝓕] where
  toFun := structureMap M (A ·) 𝓕
  map_zero' := rfl
  map_one' := rfl
  map_mul' := sorry
  map_add' := sorry

end structure_map

section single

variable {ι : Type*} [DecidableEq ι] (A : ι → Type*) {𝓕 : Filter ι}
    {S : ι → Type*}
    [(i : ι) → SetLike (S i) (A i)] {B : (i : ι) → S i} (j : ι) [(i : ι) → AddMonoid (A i)]
    [∀ (i : ι), AddSubmonoidClass (S i) (A i)]

end single

end RestrictedProduct
