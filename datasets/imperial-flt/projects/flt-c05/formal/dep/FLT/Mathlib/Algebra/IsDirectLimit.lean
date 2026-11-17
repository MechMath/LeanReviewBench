module

public import Mathlib.Algebra.Colimit.Module

@[expose] public section

variable {ι : Type*} [Preorder ι] {M : ι → Type*} {P : Type*}
  (f : (i j : ι) → (h : i ≤ j) → M i → M j) (g : ∀ i, M i → P)

/--
`IsDirectLimit f g` states that `P` is the direct limit of the system `(M i, f i j hij)`.
It requires:
* `surj`: says every element of `P` comes from some `M i` via the canonical map `g i`.
* `inj`: says that if two elements of (possibly different) modules `M i` and `M j` map
  to the same element of `P`, then they become equal after being mapped into a common
  later module `M k`.
* `compatibility`: ensures that the maps `g i` and `f i j hij` are compatible with one another.
-/
@[mk_iff] class IsDirectLimit [DirectedSystem M f] : Prop where
  surj : ∀ m : P, ∃ i, ∃ mi : M i, g i mi = m
  inj :  ∀ i j, ∀ mi : M i, ∀ mj : M j, g i mi = g j mj → ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k),
      f i k hik mi = f j k hjk mj
  compatibility : ∀ i j hij x, g j (f i j hij x) = g i x

variable [DirectedSystem M f] [IsDirectLimit f g]

namespace IsDirectLimit

include f in
theorem is_surjective : ∀ m : P, ∃ i, ∃ mi : M i, g i mi = m := sorry

/--
Given an element `p : P` in the direct limit, `preimageIndex f g p` returns an index in `ι` such
that `p` is in the image of the map `g (preimageIndex f g p) : M (preimageIndex f g p) →ₗ[R] P`.
-/
noncomputable def preimageIndex (p : P) : ι := (is_surjective f g p).choose

/--
Given an element `p : P` in the direct limit, `preimage f g p` returns an element of
`M (preimageIndex f g p)` that maps to `p` under `g (preimageIndex f g p)`.
-/
noncomputable def preimage (p : P) : M (preimageIndex f g p) :=
  (is_surjective f g p).choose_spec.choose

variable {P₁ P₂ : Type*} (g₁ : ∀ i, M i → P₁) (g₂ : ∀ i, M i → P₂)

/--
Construct a map `P₁ → P₂` from a direct limit by sending each element to its preimage
in some component `M i` and applying `g₂ i`. Used to define morphisms out of direct limits.
-/
noncomputable def lift [IsDirectLimit f g₁] (p : P₁) : P₂ :=
  g₂ (preimageIndex f g₁ p) (preimage f g₁ p)

/-- Any two direct limits of the same directed system are isomorphic. -/
noncomputable def Equiv [h₁ : IsDirectLimit f g₁] [h₂ : IsDirectLimit f g₂] :
    P₁ ≃ P₂ where
  toFun := lift f g₁ g₂
  invFun := lift f g₂ g₁
  left_inv x := sorry
  right_inv x := sorry

namespace Module

variable {R : Type*} [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [AddCommMonoid P] [Module R P] (f : (i j : ι) → i ≤ j → M i →ₗ[R] M j)
  [DirectedSystem M (f · · ·)] [IsDirectLimit (fun ⦃i j⦄ h => f i j h) g] [IsDirected ι (· ≤ ·)]

instance [DecidableEq ι] [Nonempty ι] :
    IsDirectLimit (f · · ·) (Module.DirectLimit.of R ι M f ·) := sorry

variable [AddCommMonoid P₁] [Module R P₁] [AddCommMonoid P₂] [Module R P₂]
  (g₁ : ∀ i, M i →ₗ[R] P₁) (g₂ : ∀ i, M i →ₗ[R] P₂) [h₁ : IsDirectLimit (f · · ·) (g₁ · ·)]

/--
The universal property of the direct limit: define a linear map from the direct limit
by giving a compatible family of linear maps from the components.
Each element of the limit is sent according to its representative in some component.
-/
noncomputable def lift
    (Hg : ∀ i j hij x, g₂ j (f i j hij x) = g₂ i x) : P₁ →ₗ[R] P₂ where
  toFun := IsDirectLimit.lift (f · · ·) (g₁ · ·) (g₂ · · )
  map_add' x y := sorry
  map_smul' r x := sorry

variable [h₂ : IsDirectLimit (f · · ·) (g₂ · ·)]

end Module

end IsDirectLimit
