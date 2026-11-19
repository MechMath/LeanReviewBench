import dep.DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.ApplyInput
import dep.DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.ModelBridge
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

theorem nablaRS_coordFrame_slots {r s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (x₀ : M) (hderiv : ModelDerivEqCoordDerivRSAt (I := I) X x₀ (fun x => T x))
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponentRSAt (I := I)
        (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s cov X T x₀)
        upper lower =
      coordDerivRSAt (I := I) (fun x => X x) x₀ (fun x => T x) upper lower
      +
      ∑ a : Fin r, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) k (upper a) *
          coordComponentRSAt (I := I) (T x₀) (Function.update upper a k) lower
      -
      ∑ b : Fin s, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) (lower b) k *
          coordComponentRSAt (I := I) (T x₀) upper (Function.update lower b k)  := by sorry

theorem nablaRS_coordFrame_slots_of_smooth {r s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (x₀ : M)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponentRSAt (I := I)
        (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s cov X T x₀)
        upper lower =
      coordDerivRSAt (I := I) (fun x => X x) x₀ (fun x => T x) upper lower
      +
      ∑ a : Fin r, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) k (upper a) *
          coordComponentRSAt (I := I) (T x₀) (Function.update upper a k) lower
      -
      ∑ b : Fin s, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) (lower b) k *
          coordComponentRSAt (I := I) (T x₀) upper (Function.update lower b k)  := by sorry

end DifferentialGeometry.Tensor.Coordinates

