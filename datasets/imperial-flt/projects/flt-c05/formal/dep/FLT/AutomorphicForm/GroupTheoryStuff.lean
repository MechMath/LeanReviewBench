module

public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.GroupTheory.Torsion
public import Mathlib.RingTheory.UniqueFactorizationDomain.Nat

@[expose] public section

attribute [simp] Subgroup.mem_subgroupOf

/-- The maximal `p`-quotient of a group.

Note that the torsion free parts of `G` will not get quotiented out.
So `G / MaximalPQuotient` is a `p`-group only when `G` is torsion free. -/
abbrev MaximalPQuotient (G : Type*) [Group G] (p : ℕ) :=
    G ⧸ ⨅ (N : Subgroup G) (_ : N.Normal) (_ : IsPGroup p (G ⧸ N)), N

instance (G : Type*) [Group G] (p : ℕ) :
    (⨅ (N : Subgroup G) (_ : N.Normal) (_ : IsPGroup p (G ⧸ N)), N).Normal := sorry

/-- Quotient map into the maximal `p`-quotient of a group. -/
abbrev MaximalPQuotient.mk (G : Type*) [Group G] (p : ℕ) : G →* MaximalPQuotient G p :=
  QuotientGroup.mk' _

section

lemma Subgroup.IsFiniteRelIndex.of_finite {G : Type*} [Group G] (H₁ H₂ : Subgroup G)
    (h : Set.Finite (H₂ : Set G)) : H₁.IsFiniteRelIndex H₂ := sorry

section

end

section

open MonoidHom QuotientGroup Function

variable {G : Type*} [Group G] {H : Type*} [Monoid H] (φ : G →* H)

end

namespace MonoidHom

variable {G₁ G₂ G₃ : Type*} [Group G₁] [Monoid G₂] [Monoid G₃]

variable (f : G₁ →* G₂) (f_inv : G₂ → G₁)

end MonoidHom

end

instance {G H : Type*} [Group G] [Monoid H] [MulAction G H]
    [IsScalarTower G H H] [SMulCommClass G H H] :
    IsScalarTower G Hˣ Hˣ := sorry

instance Subgroup.mulActionMulOppositeNormalizerQuotient {G : Type*} [Group G] (H : Subgroup G) :
    MulAction (Subgroup.normalizer (H : Set G))ᵐᵒᵖ (G ⧸ H) where
  smul g := Quotient.map (· * g.unop) (sorry)
  mul_smul x y m := QuotientGroup.induction_on m fun z ↦ QuotientGroup.eq.mpr (sorry)
  one_smul m := QuotientGroup.induction_on m fun z ↦ QuotientGroup.eq.mpr (sorry)
