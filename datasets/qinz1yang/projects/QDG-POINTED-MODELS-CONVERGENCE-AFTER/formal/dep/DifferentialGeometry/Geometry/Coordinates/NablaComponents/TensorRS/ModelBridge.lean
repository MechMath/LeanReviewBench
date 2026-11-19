import dep.DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.Basic
open DifferentialGeometry.Tensor.Multilinear

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Tensor.Coordinates

open Bundle Set DifferentialGeometry.Tensor0SBundle DifferentialGeometry.TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]

omit [IsManifold I 2 M] in
theorem tensorRSModelAt_coordComponentRSAt {r s : ℕ} (x₀ : M)
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x₀)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    (tensorRSModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s x₀ x₀ T
      ((continuousMultilinearMapBasis
        (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper))
      (fun b : Fin s => (Module.finBasis 𝕜 E) (lower b))
    =
      coordComponentRSAt (I := I) T upper lower  := by sorry

omit [IsManifold I 2 M] in
private theorem model_RS_component_eq_coord_component_comp_eventually {r s : ℕ}
    (x₀ : M)
    (T : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r s x)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    let β₀ : Tensor0SModel r 𝕜 E :=
      (continuousMultilinearMapBasis
        (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper
    (fun y : E =>
        (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s x₀ T y β₀)
          (fun b => (Module.finBasis 𝕜 E) (lower b))) =ᶠ[
      𝓝[Set.range I] (extChartAt I x₀ x₀)]
    (fun y : E =>
        (T ((extChartAt I x₀).symm y)
          (Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
            (M := M) r x₀ β₀ ((extChartAt I x₀).symm y)))
          (fun b =>
            coordinateFrameAt (I := I) x₀ (lower b)
              ((extChartAt I x₀).symm y)))  := by sorry

omit [IsManifold I 2 M] in
theorem modelDeriv_eq_coordDerivRSAt {r s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M)
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s) :
    ModelDerivEqCoordDerivRSAt (I := I) X x₀ (fun x => T x)  := by sorry

end DifferentialGeometry.Tensor.Coordinates

