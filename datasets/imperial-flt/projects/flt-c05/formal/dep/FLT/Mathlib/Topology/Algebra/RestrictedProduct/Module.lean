module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import dep.FLT.Deformations.ContinuousRepresentation.IsTopologicalModule
public import dep.FLT.Mathlib.Algebra.Algebra.Tower
public import dep.FLT.Mathlib.Algebra.Module.Submodule.Basic
public import dep.FLT.Mathlib.Order.Filter.Cofinite
public import dep.FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
public import dep.FLT.Mathlib.Topology.Algebra.MulAction
public import dep.FLT.Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import dep.FLT.Mathlib.Topology.Algebra.RestrictedProduct.Equiv
public import dep.FLT.Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

@[expose] public section

set_option backward.isDefEq.respectTransparency false

set_option backward.defeqAttrib.useBackward true

namespace RestrictedProduct

variable {ι : Type*}

variable {R : ι → Type*} [Π i, Ring (R i)]

variable {S : ι → Type*}

variable [Π i, SetLike (S i) (R i)] [∀ i, SubringClass (S i) (R i)]

variable {B : Π i, S i}

variable {ℱ : Filter ι}

variable {M : ι → Type*} [Π i, AddCommGroup (M i)] [Π i, Module (R i) (M i)]

variable {N : ι → Type*}

variable [Π i, SetLike (N i) (M i)] [∀ i, AddSubgroupClass (N i) (M i)]

variable [∀ i, SMulMemClass (N i) (B i) (M i)]

variable {C : Π i, N i}

instance : SMul (Πʳ i, [R i, B i]_[ℱ]) (Πʳ i, [M i, C i]_[ℱ]) where
  smul r m := ⟨fun i ↦ (r i) • (m i), sorry⟩

instance : Module (Πʳ i, [R i, B i]_[ℱ]) (Πʳ i, [M i, C i]_[ℱ]) where
  zero_smul m := sorry
  smul_zero r := sorry
  one_smul m := sorry
  add_smul r s m:= sorry
  smul_add r m n := sorry
  mul_smul r s m := sorry

variable {M₂ : ι → Type*} [Π i, AddCommGroup (M₂ i)] [Π i, Module (R i) (M₂ i)]

variable {N₂ : ι → Type*}

variable [Π i, SetLike (N₂ i) (M₂ i)] [∀ i, AddSubgroupClass (N₂ i) (M₂ i)]

variable [∀ i, SMulMemClass (N₂ i) (B i) (M₂ i)]

variable {C₂ : Π i, N₂ i}

section components

variable [DecidableEq ι]

end components

variable [Π i, TopologicalSpace (R i)] [Π i, TopologicalSpace (M i)]

section continuous_smul

variable [∀ i, ContinuousSMul (R i) (M i)] (T : Set ι)

open scoped Filter in
instance : ContinuousSMul (Πʳ i, [R i, B i]_[𝓟 T]) (Πʳ i, [M i, C i]_[𝓟 T]) := sorry

variable [hBopen : Fact (∀ i, IsOpen (B i : Set (R i)))]

variable [hCopen : Fact (∀ i, IsOpen (C i : Set (M i)))]

instance :
    ContinuousSMul (Πʳ i, [R i, B i]) (Πʳ i, [M i, C i]) := sorry

end continuous_smul

section components

variable [Π i, TopologicalSpace (M₂ i)]

end components

section free_topology

variable (n : Type*)

variable (B) in
/-- If `B i` is subring of `R i` then `(B i)^n` is a `B i`-submodule of `(R i)^n`. -/
def piSubringSubmodule (i : ι) : Submodule (B i) (n → R i) :=
  Submodule.pi Set.univ fun (_ : n) ↦ Subring.toSubmodule (Subring.ofClass (B i))

/-- Canonical linear equivalence between `Π' R^n` and `(Π' R)^n` -/
def _root_.LinearEquiv.restrictedProductPi [Fintype n] :
    Πʳ i, [n → R i, piSubringSubmodule B n i]_[ℱ] ≃ₗ[Πʳ i, [R i, B i]_[ℱ]]
      n → Πʳ i, [R i, B i]_[ℱ] where
  toFun x j := map (fun i y ↦ y j)
    (sorry)
    x
  invFun x := ⟨fun i j ↦ x j i, sorry⟩
  map_add' x y := rfl
  map_smul' x y := rfl

variable [∀ i, IsTopologicalRing (R i)]

/-- Canonical continuous linear equivalence between `Π' R^n` and `(Π' R)^n` -/
def _root_.ContinuousLinearEquiv.restrictedProductPi [Fintype n]
    (hOpen : ∀ i, IsOpen (B i : Set (R i))) :
    Πʳ i, [n → R i, piSubringSubmodule B n i] ≃L[Πʳ i, [R i, B i]] n → Πʳ i, [R i, B i] where
  __ := LinearEquiv.restrictedProductPi n
  continuous_toFun := sorry
  continuous_invFun := sorry

end free_topology

variable [∀ i, IsTopologicalRing (R i)]

variable [∀ i, IsModuleTopology (R i) (M i)]

variable [Module.Finite (Πʳ i, [R i, B i]) (Πʳ i, [M i, C i])]

end RestrictedProduct
