



import dep.DifferentialGeometry.Tensor.Alternating.Composition
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Data.Bundle

noncomputable section

open Bundle Set

section defs
variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] (s : ℕ)
variable {B : Type*}

@[reducible]
protected def Bundle.continuousMultilinearMap (_F : Type*) (E : B → Type*)
    [Π x, AddCommMonoid (E x)] [Π x, Module 𝕜 (E x)] [Π x, TopologicalSpace (E x)]
    (x : B) : Type _ :=
  let _ := _F
  ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜

variable (F : Type*) (E : B → Type*) [Π x, AddCommMonoid (E x)] [Π x, Module 𝕜 (E x)]
variable [Π x, TopologicalSpace (E x)]

instance Bundle.continuousMultilinearMap.instAddCommMonoid (x : B) :
    AddCommMonoid (Bundle.continuousMultilinearMap 𝕜 s F E x) := by
  dsimp [Bundle.continuousMultilinearMap]; infer_instance

instance Bundle.continuousMultilinearMap.instModule (x : B) :
    Module 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) :=
  inferInstanceAs (Module 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜))

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

def continuousMultilinearMapCoordChange (b : B) : MLF →L[𝕜] MLF :=
  ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin s => e'.coordChangeL 𝕜 e b)

variable [∀ x, TopologicalSpace (E x)] [FiberBundle F E]

theorem continuousOn_continuousMultilinearMapCoordChange
    [VectorBundle 𝕜 F E] [MemTrivializationAtlas e] [MemTrivializationAtlas e'] :
    ContinuousOn (continuousMultilinearMapCoordChange 𝕜 s e e')
      (e.baseSet ∩ e'.baseSet)  := by sorry

def continuousMultilinearMap : Pretrivialization MLF
    (π MLF (Bundle.continuousMultilinearMap 𝕜 s F E)) where
  toFun p := ⟨p.1, p.2.compContinuousLinearMap (fun _ => e.symmL 𝕜 p.1)⟩
  invFun p := ⟨p.1, p.2.compContinuousLinearMap (fun _ => e.continuousLinearMapAt 𝕜 p.1)⟩
  source := (Bundle.TotalSpace.proj) ⁻¹' e.baseSet
  target := e.baseSet ×ˢ Set.univ
  map_source' _ h := ⟨h, Set.mem_univ _⟩
  map_target' _ h := h.1
  left_inv' := fun ⟨x, L⟩ h ↦ by
    rw [TotalSpace.mk_inj]
    dsimp [Bundle.continuousMultilinearMap]
    ext v
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    exact e.symmₗ_linearMapAt h (v i)
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

instance continuousMultilinearMap.isLinear :
    (Pretrivialization.continuousMultilinearMap 𝕜 s e).IsLinear 𝕜 where
  linear _ _ :=
  { map_add := fun _ _ ↦ rfl
    map_smul := fun _ _ ↦ by ext; rfl }

theorem continuousMultilinearMap_apply
    (p : TotalSpace MLF (Bundle.continuousMultilinearMap 𝕜 s F E)) :
    (continuousMultilinearMap 𝕜 s e) p =
    ⟨p.1, p.2.compContinuousLinearMap (fun _ => e.symmL 𝕜 p.1)⟩  := by sorry

theorem continuousMultilinearMap_symm_apply (p : B × MLF) :
    (continuousMultilinearMap 𝕜 s e).toPartialEquiv.symm p =
    ⟨p.1, p.2.compContinuousLinearMap (fun _ => e.continuousLinearMapAt 𝕜 p.1)⟩  := by sorry

@[simp] theorem baseSet_continuousMultilinearMap :
    (Pretrivialization.continuousMultilinearMap 𝕜 s e).baseSet = e.baseSet  := by sorry

theorem continuousMultilinearMap_symm_apply_of_mem {b : B} (hb : b ∈ e.baseSet) (L : MLF) :
    (continuousMultilinearMap 𝕜 s e).symm b L =
    L.compContinuousLinearMap (fun _ => e.continuousLinearMapAt 𝕜 b)  := by sorry

theorem continuousMultilinearMapCoordChange_apply (b : B)
    (hb : b ∈ e.baseSet ∩ e'.baseSet) (L : MLF) :
    continuousMultilinearMapCoordChange 𝕜 s e e' b L =
    (continuousMultilinearMap 𝕜 s e'
      (TotalSpace.mk b ((continuousMultilinearMap 𝕜 s e).symm b L))).2  := by sorry

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
  pretrivialization_linear' := by
    rintro _ ⟨e, he, rfl⟩
    have := he
    exact Pretrivialization.continuousMultilinearMap.isLinear 𝕜 s e
  pretrivializationAt x := Pretrivialization.continuousMultilinearMap 𝕜 s
    (trivializationAt F E x)
  mem_base_pretrivializationAt x := mem_baseSet_trivializationAt F E x
  pretrivialization_mem_atlas x :=
    ⟨trivializationAt F E x, inferInstance, rfl⟩
  exists_coordChange := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    have := he; have := he'
    exact ⟨continuousMultilinearMapCoordChange 𝕜 s e e',
      continuousOn_continuousMultilinearMapCoordChange 𝕜 s e e',
      continuousMultilinearMapCoordChange_apply 𝕜 s e e'⟩
  totalSpaceMk_isInducing x := ⟨rfl⟩

instance Bundle.continuousMultilinearMap.topologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace MLF (Bundle.continuousMultilinearMap 𝕜 s F E)) :=
  (Bundle.continuousMultilinearMap.vectorPrebundle 𝕜 s F E).totalSpaceTopology

instance _root_.Bundle.continuousMultilinearMap.fiberBundle :
    FiberBundle MLF (Bundle.continuousMultilinearMap 𝕜 s F E) :=
  (Bundle.continuousMultilinearMap.vectorPrebundle 𝕜 s F E).toFiberBundle

instance _root_.Bundle.continuousMultilinearMap.vectorBundle :
    VectorBundle 𝕜 MLF (Bundle.continuousMultilinearMap 𝕜 s F E) :=
  (Bundle.continuousMultilinearMap.vectorPrebundle 𝕜 s F E).toVectorBundle

variable [he : MemTrivializationAtlas e] {F E}

def Bundle.Trivialization.continuousMultilinearMap :
    Trivialization MLF (π MLF (Bundle.continuousMultilinearMap 𝕜 s F E)) :=
  VectorPrebundle.trivializationOfMemPretrivializationAtlas _ ⟨e, he, rfl⟩

instance _root_.Bundle.continuousMultilinearMap.memTrivializationAtlas :
    MemTrivializationAtlas (e.continuousMultilinearMap 𝕜 s :
    Trivialization MLF (π MLF (Bundle.continuousMultilinearMap 𝕜 s F E))) where
  out := ⟨_, ⟨e, inferInstance, rfl⟩, rfl⟩

@[simp] theorem Bundle.Trivialization.baseSet_continuousMultilinearMap :
    (e.continuousMultilinearMap 𝕜 s).baseSet = e.baseSet  := by sorry

theorem Bundle.Trivialization.continuousMultilinearMap_apply
    (p : TotalSpace MLF (Bundle.continuousMultilinearMap 𝕜 s F E)) :
    e.continuousMultilinearMap 𝕜 s p =
    ⟨p.1, p.2.compContinuousLinearMap (fun _ => e.symmL 𝕜 p.1)⟩  := by sorry

end

section smooth

open scoped Bundle Manifold

open Bundle Set Pretrivialization

variable {𝕜 B F : Type*} {E : B → Type*} (s : ℕ)
  [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  (IB : ModelWithCorners 𝕜 EB HB)
  [TopologicalSpace B] [ChartedSpace HB B]
  [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace (Bundle.TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  {e e' : Trivialization F (π F E)}
  [FiniteDimensional 𝕜 F]
  (n : WithTop ℕ∞)

local notation "MLF" => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
theorem contMDiffOn_continuousMultilinearMapCoordChange
    [ContMDiffVectorBundle n F E IB]
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] :
    ContMDiffOn IB 𝓘(𝕜, MLF →L[𝕜] MLF) n
      (continuousMultilinearMapCoordChange 𝕜 s e e')
      (e.baseSet ∩ e'.baseSet)  := by sorry

variable [ContMDiffVectorBundle n F E IB]

instance Bundle.continuousMultilinearMap.vectorPrebundle.isSmooth :
    (Bundle.continuousMultilinearMap.vectorPrebundle 𝕜 s F E).IsContMDiff IB n where
  exists_contMDiffCoordChange := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    have := he; have := he'
    refine ⟨continuousMultilinearMapCoordChange 𝕜 s e e',
      contMDiffOn_continuousMultilinearMapCoordChange s IB n, ?_⟩
    rintro b hb v
    exact continuousMultilinearMapCoordChange_apply 𝕜 s e e' b hb v

instance SmoothVectorBundle.continuousMultilinearMap :
    ContMDiffVectorBundle n MLF (Bundle.continuousMultilinearMap 𝕜 s F E) IB :=
  (Bundle.continuousMultilinearMap.vectorPrebundle 𝕜 s F E).contMDiffVectorBundle IB

end smooth

