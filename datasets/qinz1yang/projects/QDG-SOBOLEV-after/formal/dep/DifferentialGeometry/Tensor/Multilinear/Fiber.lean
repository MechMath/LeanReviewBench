
import dep.DifferentialGeometry.Tensor.Multilinear.Bundle
import dep.DifferentialGeometry.Tensor.Multilinear.Basis


noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set

open scoped Manifold Topology Bundle ContDiff BigOperators

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]
variable {s : ℕ}


instance instFunLike (s : ℕ) (x : B) :
    FunLike (Bundle.continuousMultilinearMap 𝕜 s F E x) (Fin s → E x) 𝕜 :=
  ContinuousMultilinearMap.funLike



set_option backward.isDefEq.respectTransparency false in

theorem topology_eq (s : ℕ) (x : B) :
    (inferInstance : TopologicalSpace (Bundle.continuousMultilinearMap 𝕜 s F E x)) =
    (inferInstanceAs (TopologicalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜)))  := by sorry

instance instNormedAddCommGroup (s : ℕ) (x : B) :
    NormedAddCommGroup (Bundle.continuousMultilinearMap 𝕜 s F E x) := by
  delta Bundle.continuousMultilinearMap; infer_instance


instance instNormedSpace (s : ℕ) (x : B) :
    NormedSpace 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) := by
  delta Bundle.continuousMultilinearMap; exact ContinuousMultilinearMap.normedSpace



instance instT2Space (s : ℕ) (x : B) :
    @T2Space (Bundle.continuousMultilinearMap 𝕜 s F E x) inferInstance :=
  (topology_eq (𝕜 := 𝕜) (F := F) (E := E) s x).symm ▸
    inferInstanceAs (@T2Space (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) _)

instance instIsTopologicalAddGroup (s : ℕ) (x : B) :
    @IsTopologicalAddGroup (Bundle.continuousMultilinearMap 𝕜 s F E x) inferInstance _ :=
  (topology_eq (𝕜 := 𝕜) (F := F) (E := E) s x).symm ▸
    inferInstanceAs (@IsTopologicalAddGroup
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) _ _)

instance instContinuousSMul (s : ℕ) (x : B) :
    @ContinuousSMul 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) _ _ inferInstance :=
  (topology_eq (𝕜 := 𝕜) (F := F) (E := E) s x).symm ▸
    inferInstanceAs (@ContinuousSMul 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) _ _ _)

instance instContinuousAdd (s : ℕ) (x : B) :
    @ContinuousAdd (Bundle.continuousMultilinearMap 𝕜 s F E x) inferInstance _ :=
  @IsTopologicalAddGroup.toContinuousAdd _ inferInstance _ (instIsTopologicalAddGroup s x)




def continuousLinearEquivAt (s : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 s F E x ≃L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 where
  toFun := ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ => (trivializationAt F E x).symmL 𝕜 x)
  invFun := ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ => (trivializationAt F E x).continuousLinearMapAt 𝕜 x)
  left_inv L := ContinuousMultilinearMap.ext fun v => by
    dsimp [ContinuousMultilinearMap.compContinuousLinearMapL]
    congr 1; funext i
    exact (trivializationAt F E x).symmₗ_linearMapAt
      (mem_baseSet_trivializationAt F E x) (v i)
  right_inv M := ContinuousMultilinearMap.ext fun v => by
    dsimp [ContinuousMultilinearMap.compContinuousLinearMapL]
    congr 1; funext i
    exact (trivializationAt F E x).linearMapAt_symmₗ
      (mem_baseSet_trivializationAt F E x) (v i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by
    change @Continuous (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x)
      ContinuousMultilinearMap.instTopologicalSpace _
    rw [show instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x =
      ContinuousMultilinearMap.instTopologicalSpace from topology_eq s x]
    exact (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ => (trivializationAt F E x).symmL 𝕜 x)).continuous
  continuous_invFun := by
    change @Continuous (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (Bundle.continuousMultilinearMap 𝕜 s F E x)
      ContinuousMultilinearMap.instTopologicalSpace
      (instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x) _
    rw [show instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x =
      ContinuousMultilinearMap.instTopologicalSpace from topology_eq s x]
    exact (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ => (trivializationAt F E x).continuousLinearMapAt 𝕜 x)).continuous



omit [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E] in
@[ext]
theorem ext {s : ℕ} {x : B}
    {T₁ T₂ : Bundle.continuousMultilinearMap 𝕜 s F E x}
    (h : ∀ m, T₁ m = T₂ m) : T₁ = T₂  := by sorry

theorem triv_zero_apply_eq (x₀ x : B)
    (T : Bundle.continuousMultilinearMap 𝕜 0 F E x)
    (w : Fin 0 → F) :
    (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
      (Bundle.continuousMultilinearMap 𝕜 0 F E) x₀ ⟨x, T⟩).2 w = T Fin.elim0  := by sorry

theorem triv_zero_symmL_apply_elim0 (x₀ x : B)
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (ω₀ : ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜) :
    ((trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 0 F E) x₀).symmL 𝕜 x ω₀ :
        Bundle.continuousMultilinearMap 𝕜 0 F E x) Fin.elim0 = ω₀ 0  := by sorry

theorem triv_symmL_eq_compContinuousLinearMap {s : ℕ} (x₀ x : B)
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :
    ((trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 s F E) x₀).symmL 𝕜 x T :
        Bundle.continuousMultilinearMap 𝕜 s F E x) =
      T.compContinuousLinearMap
        (fun _ : Fin s => (trivializationAt F E x₀).continuousLinearMapAt 𝕜 x)  := by sorry

def toModel {s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 :=
  continuousLinearEquivAt (F := F) (E := E) s x T


def toModelL (s : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 s F E x →L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 :=
  (continuousLinearEquivAt (F := F) (E := E) s x).toContinuousLinearMap


def ofModel {s : ℕ} {x : B}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :
    Bundle.continuousMultilinearMap 𝕜 s F E x :=
  (continuousLinearEquivAt (F := F) (E := E) s x).symm f

@[simp]
theorem toModelL_apply {s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    toModelL (F := F) (E := E) s x T = toModel T  := by sorry

@[simp]
theorem toModel_add {s : ℕ} {x : B}
    (T₁ T₂ : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    toModel (F := F) (E := E) (T₁ + T₂) =
      toModel T₁ + toModel T₂  := by sorry

@[simp]
theorem toModel_smul {s : ℕ} {x : B}
    (c : 𝕜) (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    toModel (F := F) (E := E) (c • T) = c • toModel T  := by sorry

@[simp]
theorem toModel_zero {s : ℕ} {x : B} :
    toModel (F := F) (E := E)
      (0 : Bundle.continuousMultilinearMap 𝕜 s F E x) = 0  := by sorry

@[simp]
theorem toModel_neg {s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    toModel (F := F) (E := E) (-T) = -toModel T  := by sorry

@[simp]
theorem toModel_sub {s : ℕ} {x : B}
    (T₁ T₂ : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    toModel (F := F) (E := E) (T₁ - T₂) =
      toModel T₁ - toModel T₂  := by sorry

@[simp]
theorem ofModel_toModel {s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    ofModel (F := F) (E := E) (toModel T) = T  := by sorry

@[simp]
theorem toModel_ofModel {s : ℕ} {x : B}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :
    toModel (F := F) (E := E) (ofModel (x := x) f) = f  := by sorry

theorem toModel_continuous {s : ℕ} {x : B} :
    Continuous
      (fun T : Bundle.continuousMultilinearMap 𝕜 s F E x =>
        toModel (F := F) (E := E) T)  := by sorry

theorem toModel_injective {s : ℕ} {x : B} :
    Function.Injective
      (fun T : Bundle.continuousMultilinearMap 𝕜 s F E x =>
        toModel (F := F) (E := E) T)  := by sorry

theorem toModel_surjective {s : ℕ} {x : B} :
    Function.Surjective
      (fun T : Bundle.continuousMultilinearMap 𝕜 s F E x =>
        toModel (F := F) (E := E) T)  := by sorry

theorem toModel_bijective {s : ℕ} {x : B} :
    Function.Bijective
      (fun T : Bundle.continuousMultilinearMap 𝕜 s F E x =>
        toModel (F := F) (E := E) T)  := by sorry

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

noncomputable instance instFiniteDimensional (s : ℕ) (x : B) :
    FiniteDimensional 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) := by
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional s
  exact (continuousLinearEquivAt (F := F) (E := E) s x).symm.toLinearEquiv.finiteDimensional

@[simp]
theorem finrank_eq (s : ℕ) (x : B) :
    Module.finrank 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) =
    (Module.finrank 𝕜 F) ^ s  := by sorry

end Bundle.continuousMultilinearMap

end
