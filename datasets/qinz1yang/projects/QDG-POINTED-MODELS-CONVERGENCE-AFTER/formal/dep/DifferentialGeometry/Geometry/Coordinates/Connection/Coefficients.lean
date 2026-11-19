import dep.DifferentialGeometry.Geometry.Coordinates.Connection.Christoffel
import dep.DifferentialGeometry.Geometry.Coordinates.Frame.Coordinate
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Tensor.Coordinates

open Bundle Set DifferentialGeometry.TensorLieDeriv Filter
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]

omit [IsManifold I 2 M] in
omit [CompleteSpace 𝕜] in
theorem tangentConstInChart_eq_coordinateFrame_eventually
    (x₀ : M) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ ((Module.finBasis 𝕜 E) i) :
        (x : M) → TangentSpace I x) =ᶠ[𝓝 x₀]
      coordinateFrameAt (I := I) x₀ i  := by sorry

theorem connCoeff_eq_christoffelAlong_coord
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : (x : M) -> TangentSpace I x) (x₀ : M)
    (j k : CoordinateIdx (𝕜 := 𝕜) E) :
    connectionEndomorphismCoeff (𝕜 := 𝕜) (E := E) (Module.finBasis 𝕜 E)
        (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x₀
          (extChartAt I x₀ x₀)) j k =
      christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
        x₀ (X x₀) j k  := by sorry

end DifferentialGeometry.Tensor.Coordinates

