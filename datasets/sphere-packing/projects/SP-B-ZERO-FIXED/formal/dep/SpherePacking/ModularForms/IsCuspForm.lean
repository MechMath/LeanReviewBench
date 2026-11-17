module

public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
public import Mathlib.NumberTheory.ModularForms.QExpansion

@[expose] public section

open ModularForm UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups Manifold

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat CongruenceSubgroup Manifold

noncomputable section Definitions

variable {α ι : Type*}

open SlashInvariantFormClass ModularFormClass

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)

def ModForm_mk (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : CuspForm Γ k) : ModularForm Γ k where
  toFun := f
  slash_action_eq' := f.slash_action_eq'
  holo' := f.holo'
  bdd_at_cusps' := fun hc ↦ bdd_at_cusps f hc

def CuspForm_to_ModularForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ) : CuspForm Γ k →ₗ[ℂ] ModularForm Γ k
  where
  toFun f := ModForm_mk Γ k f
  map_add' := by
    intro f g
    simp only [ModForm_mk, FunLike.coe_add]
    rfl
  map_smul' := by
    intro m f
    simp only [ModForm_mk, RingHom.id_apply]
    rfl

def CuspFormSubmodule (Γ : Subgroup SL(2, ℤ)) (k : ℤ) : Submodule ℂ (ModularForm Γ k) :=
  LinearMap.range (CuspForm_to_ModularForm Γ k)

instance (priority := 100) CuspFormSubmodule.funLike :
    FunLike (CuspFormSubmodule Γ k) ℍ ℂ where
  coe f := f.1.toFun
  coe_injective f g h := by cases f; cases g; congr; exact DFunLike.ext' h

instance (Γ : Subgroup SL(2, ℤ)) (k : ℤ) : CuspFormClass (CuspFormSubmodule Γ k) Γ k := sorry
