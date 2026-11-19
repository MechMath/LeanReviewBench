import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.Model.TensorRS
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.InducedConnection

namespace DifferentialGeometry
namespace TensorLieDeriv

noncomputable section


open Bundle Set IsManifold ContinuousLinearMap VectorField Filter
    DifferentialGeometry.Tensor0SBundle Function
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I n M]
variable {x x₀ : M} {s : Set M}

variable [CompleteSpace 𝕜]

section ModelCovariantDerivative

theorem contDiffWithinAt_covariantDeriv_tensor0SModelWithin (s : ℕ)
    {m n' : WithTop ℕ∞} {X : E → E} {ΓX : E → E →L[𝕜] E}
    {α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s}
    {u : Set E} {x : E}
    (hα : ContDiffWithinAt 𝕜 n' α u x)
    (hX : ContDiffWithinAt 𝕜 m X u x)
    (hΓ : ContDiffWithinAt 𝕜 m ΓX u x)
    (hu : UniqueDiffOn 𝕜 u) (hmn : m + 1 ≤ n') (hx : x ∈ u) :
    ContDiffWithinAt 𝕜 m
      (fun y => covariantDerivTensor0SModelWithin (𝕜 := 𝕜) (E := E)
        s X ΓX α u y) u x  := by sorry

theorem contDiffWithinAt_covariantDeriv_tensorRSModelWithin (r s : ℕ)
    {m n' : WithTop ℕ∞} {X : E → E} {ΓX : E → E →L[𝕜] E}
    {T : E → TensorRSModel r s 𝕜 E}
    {u : Set E} {x : E}
    (hT : ContDiffWithinAt 𝕜 n' T u x)
    (hX : ContDiffWithinAt 𝕜 m X u x)
    (hΓ : ContDiffWithinAt 𝕜 m ΓX u x)
    (hu : UniqueDiffOn 𝕜 u) (hmn : m + 1 ≤ n') (hx : x ∈ u) :
    ContDiffWithinAt 𝕜 m
      (fun y => covariantDerivTensorRSModelWithin (𝕜 := 𝕜) (E := E)
        r s X ΓX T u y) u x  := by sorry

end ModelCovariantDerivative

end

end TensorLieDeriv
end DifferentialGeometry

