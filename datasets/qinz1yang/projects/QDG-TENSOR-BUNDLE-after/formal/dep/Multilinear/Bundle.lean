


import Mathlib
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Data.Bundle



























noncomputable section

open Bundle Set



section defs
variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] (s : ℕ)
variable {B : Type*}

set_option linter.unusedVariables false in





protected def Bundle.continuousMultilinearMap (F : Type*) (E : B → Type*)
    [Π x, AddCommMonoid (E x)] [Π x, Module 𝕜 (E x)] [Π x, TopologicalSpace (E x)]
    (x : B) : Type _ :=
  ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜

variable (F : Type*) (E : B → Type*) [Π x, AddCommMonoid (E x)] [Π x, Module 𝕜 (E x)]
variable [Π x, TopologicalSpace (E x)]

instance Bundle.continuousMultilinearMap.instAddCommMonoid (x : B) :
    AddCommMonoid (Bundle.continuousMultilinearMap 𝕜 s F E x) := by
  dsimp [Bundle.continuousMultilinearMap]; infer_instance

instance Bundle.continuousMultilinearMap.instModule (x : B) :
    Module 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) := by
  dsimp [Bundle.continuousMultilinearMap]; infer_instance

end defs



variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] (s : ℕ)
variable {B : Type*} [TopologicalSpace B]
variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (E : B → Type*) [Π x, AddCommMonoid (E x)] [Π x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]


local notation "MLF" => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜

variable {F E}
variable (e e' : Trivialization F (π F E))

namespace Pretrivialization

variable [e.IsLinear 𝕜] [e'.IsLinear 𝕜]




variable [∀ x, TopologicalSpace (E x)] [FiberBundle F E]



def continuousMultilinearMap : Pretrivialization MLF
    (π MLF (Bundle.continuousMultilinearMap 𝕜 s F E)) where
  toFun p := ⟨p.1, p.2.compContinuousLinearMap (fun _ => e.symmL 𝕜 p.1)⟩
  invFun p := ⟨p.1, p.2.compContinuousLinearMap (fun _ => e.continuousLinearMapAt 𝕜 p.1)⟩
  source := (Bundle.TotalSpace.proj) ⁻¹' e.baseSet
  target := e.baseSet ×ˢ Set.univ
  map_source' _ h := ⟨h, Set.mem_univ _⟩
  map_target' _ h := h.1
  left_inv' := by sorry
  right_inv' := fun ⟨x, f⟩ ⟨hx, _⟩ ↦ by
    ext v
    · rfl
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    exact e.linearMapAt_symmₗ hx (v i)
  open_target := e.open_baseSet.prod isOpen_univ
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl


end Pretrivialization



open Pretrivialization
variable (F E)
variable [Π x : B, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle 𝕜 F E]


instance (x : B) : TopologicalSpace (Bundle.continuousMultilinearMap 𝕜 s F E x) :=
  TopologicalSpace.induced
    ((Pretrivialization.continuousMultilinearMap 𝕜 s
      (trivializationAt F E x)) ∘ TotalSpace.mk' MLF x)
    inferInstance



def _root_.Bundle.continuousMultilinearMap.vectorPrebundle :
    VectorPrebundle 𝕜 MLF (Bundle.continuousMultilinearMap 𝕜 s F E) where
  pretrivializationAtlas :=
    {e' | ∃ (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e),
      e' = Pretrivialization.continuousMultilinearMap 𝕜 s e}
  pretrivialization_linear' := by sorry
  pretrivializationAt x := Pretrivialization.continuousMultilinearMap 𝕜 s
    (trivializationAt F E x)
  mem_base_pretrivializationAt x := mem_baseSet_trivializationAt F E x
  pretrivialization_mem_atlas x :=
    ⟨trivializationAt F E x, inferInstance, rfl⟩
  exists_coordChange := by sorry
  totalSpaceMk_isInducing x := ⟨rfl⟩


instance Bundle.continuousMultilinearMap.topologicalSpace_totalSpace :
    TopologicalSpace (TotalSpace MLF (Bundle.continuousMultilinearMap 𝕜 s F E)) :=
  (Bundle.continuousMultilinearMap.vectorPrebundle 𝕜 s F E).totalSpaceTopology


instance _root_.Bundle.continuousMultilinearMap.fiberBundle :
    FiberBundle MLF (Bundle.continuousMultilinearMap 𝕜 s F E) :=
  (Bundle.continuousMultilinearMap.vectorPrebundle 𝕜 s F E).toFiberBundle



end
