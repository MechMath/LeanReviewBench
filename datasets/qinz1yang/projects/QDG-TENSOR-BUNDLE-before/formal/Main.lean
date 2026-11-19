import Mathlib
import dep.Defs
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

/-- The (0,0)-tensor bundle is a fiber bundle with fiber `𝕜`. -/
instance tensor0S_fiberBundle_zero :
    FiberBundle
      (Tensor0SModel 0 𝕜 E)
      (fun x : M => Tensor0SSpace 0 I x) :=
    inferInstanceAs <| FiberBundle
      (Tensor0SModel 0 𝕜 E)
      (fun _ : M => Tensor0SModel 0 𝕜 E)

/-- The (0,0)-tensor bundle is a vector bundle with model fiber `𝕜`. -/
instance tensor0S_vectorBundle_zero :
    @VectorBundle 𝕜 M (Tensor0SModel 0 𝕜 E) (fun x : M => Tensor0SSpace 0 I x) _ _ _ _
    (tensor0SModel_normedSpace 0) _ _ _ tensor0S_fiberBundle_zero := by sorry

structure Tensor0SBundleData (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (H : Type*) [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (n : WithTop ℕ∞) [IsManifold I n M]
    (s : ℕ) where
  topology : TopologicalSpace (TotalSpace
    (Tensor0SModel s 𝕜 E)
    (fun x : M => Tensor0SSpace s I x))
  fiber : FiberBundle
    (Tensor0SModel s 𝕜 E)
    (fun x : M => Tensor0SSpace s I x)
  vector : VectorBundle 𝕜
    (Tensor0SModel s 𝕜 E)
    (fun x : M => Tensor0SSpace s I x)
  smooth : ContMDiffVectorBundle n
    (Tensor0SModel s 𝕜 E)
    (fun x : M => Tensor0SSpace s I x) I

/-- The base case `s = 0` of the `Tensor0SBundleData` induction: all four bundle instances
for the trivial `𝕜`-bundle. -/
noncomputable def tensor0SBundleData_zero :
    Tensor0SBundleData (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) 0 := {
  topology := tensor0S_topologicalSpace_zero
  fiber := tensor0S_fiberBundle_zero
  vector := tensor0S_vectorBundle_zero
  smooth := inferInstanceAs <| ContMDiffVectorBundle n
    (Tensor0SModel 0 𝕜 E)
    (fun _ : M => Tensor0SModel 0 𝕜 E) I
}

/-- All four bundle instances for the (0,s)-tensor bundle, constructed inductively by
currying: a (0,s+1)-tensor bundle is the hom bundle from `TM` to the (0,s)-tensor bundle. -/
noncomputable def tensor0SBundleData : (s : ℕ) →
    Tensor0SBundleData (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
  | 0 => tensor0SBundleData_zero  (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n)
  | s + 1 => by
    let prev := tensor0SBundleData s
    refine {
      topology := ?_,
      fiber := ?_,
      vector := ?_,
      smooth := ?_
    }
    · exact inferInstanceAs <| TopologicalSpace (TotalSpace
        (Tensor0SModel (s+1) 𝕜 E) (fun _ : M => Tensor0SModel (s+1) 𝕜 E))
    · exact inferInstanceAs <| FiberBundle
        (Tensor0SModel (s+1) 𝕜 E)
        (fun x : M => Tensor0SModel (s+1) 𝕜 E)
    · exact inferInstanceAs <| VectorBundle 𝕜
        (Tensor0SModel (s+1) 𝕜 E)
        (fun x : M => Tensor0SModel (s+1) 𝕜 E)
    · exact inferInstanceAs <| ContMDiffVectorBundle n
        (Tensor0SModel (s+1) 𝕜 E)
        (fun x : M => Tensor0SModel (s+1) 𝕜 E) I

/-- The total space of the (0,s)-tensor bundle carries a topology derived from
`Tensor0SBundleData`. -/
def tensor0SBundle_topology (s : ℕ) :
    TopologicalSpace (TotalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
      (fun x : M => Tensor0SSpace s I x)) :=
  (tensor0SBundleData n s).topology

/-- The (0,s)-tensor bundle is a fiber bundle with model fiber `Tensor0SModel s 𝕜 E`. -/
noncomputable instance tensor0SBundle_smooth (s : ℕ) :
    @ContMDiffVectorBundle n 𝕜 M (Tensor0SModel s 𝕜 E) (fun x : M => Tensor0SSpace s I x)
      _ E _ _ H _ I _ _ _ _ _ _ (tensor0SBundle_topology (n := n) s) _
      (tensor0SBundleData n s).fiber (tensor0SBundleData n s).vector
  := by sorry

end
end Tensor0SBundle
