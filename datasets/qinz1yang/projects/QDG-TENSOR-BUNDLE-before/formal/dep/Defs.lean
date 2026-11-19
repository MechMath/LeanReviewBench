import Mathlib
namespace Tensor0SBundle
noncomputable section

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I ω M]
variable {x' : M}
variable {r s : ℕ}

@[reducible]
def Tensor0SModel (s : ℕ) (𝕜 : Type*) (E : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E] :=
  ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜


@[reducible]
def Tensor0SSpace (s : ℕ) (I : ModelWithCorners 𝕜 E H) (x : M) :=
  ContinuousMultilinearMap 𝕜 (fun _ : Fin s => TangentSpace I x) 𝕜


instance (s : ℕ) :
    NormedAddCommGroup (Tensor0SModel s 𝕜 E) := by
  unfold Tensor0SModel
  letI : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := inferInstance
  infer_instance


instance tensor0SModel_normedSpace (s : ℕ) :
    NormedSpace 𝕜 (Tensor0SModel s 𝕜 E) := by
  unfold Tensor0SModel
  exact @ContinuousMultilinearMap.normedSpace 𝕜 (Fin s) (fun _ : Fin s => E) 𝕜 _ _ _ _ _ _ 𝕜 _ _ _


instance tensor0S_topologicalSpace_zero :
    TopologicalSpace (TotalSpace
      (Tensor0SModel 0 𝕜 E)
      (fun x : M => Tensor0SSpace 0 I x)) :=
  inferInstanceAs <| TopologicalSpace (TotalSpace
    (Tensor0SModel 0 𝕜 E)
    (fun _ : M => Tensor0SModel 0 𝕜 E))

end
end Tensor0SBundle
