import dep.DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.Basic
open DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Geometry.Operator

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
omit [CompleteSpace 𝕜] in
private theorem coordinateFrameAt_basis_continuousLinearMapAt
    (x₀ : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := 𝕜) E) :
    (trivializationAt E (TangentSpace I : M -> Type _) x₀).continuousLinearMapAt
        𝕜 x ((coordinateFrameAtBasis (I := I) x₀ hx) i) =
      (Module.finBasis 𝕜 E) i  := by sorry

omit [IsManifold I 2 M] in
omit [CompleteSpace 𝕜] in
private theorem coordinateFrameAt_basis_repr_eq_trivializationAt
    (x₀ : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (v : TangentSpace I x) :
    (coordinateFrameAtBasis (I := I) x₀ hx).repr v =
      (Module.finBasis 𝕜 E).repr
        ((trivializationAt E (TangentSpace I : M -> Type _) x₀).continuousLinearMapAt
          𝕜 x v)  := by sorry

omit [IsManifold I 2 M] in
theorem constInChart_basisTensor0S_coordFrame {r : ℕ}
    (x₀ : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E) :
    Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) r x₀
        ((continuousMultilinearMapBasis
          (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper) x =
      basisTensor0S (I := I) (coordinateFrameAtBasis (I := I) x₀ hx) upper  := by sorry

omit [IsManifold I 2 M] in
private theorem coordFrameRSComp_at {r s : ℕ}
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (x₀ : M)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    tensorRSComponentInFrame
        (I := I) (M := M)
        (Idx := CoordinateIdx (𝕜 := 𝕜) E)
        (u := coordinateFrameSet (I := I) x₀)
        (fun x => T x)
        (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame (I := I) x₀)
        x₀ (coordinateFrameAt_mem (I := I) x₀) upper lower =
      coordComponentRSAt (I := I) (T x₀) upper lower  := by sorry

omit [IsManifold I 2 M] in
theorem applyInput_coordFrame_eventually {r s : ℕ}
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (θ : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r)
    (x₀ : M) (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    (fun y : M =>
        (T y (θ y))
          (fun b : Fin s => coordinateFrameAt (I := I) x₀ (lower b) y))
      =ᶠ[𝓝 x₀]
    (fun y : M =>
      ∑ upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E,
        θ y (fun a : Fin r => coordinateFrameAt (I := I) x₀ (upper a) y) *
          (T y
            (Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H)
              (I := I) (M := M) r x₀
              ((continuousMultilinearMapBasis
                (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper) y))
            (fun b : Fin s => coordinateFrameAt (I := I) x₀ (lower b) y))  := by sorry

omit [IsManifold I 2 M] in
theorem tensorRS_eval_constInChart_coordinateFrame_contMDiffAt {r s : ℕ}
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (x₀ : M)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun y : M =>
        (T y
          (Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H)
            (I := I) (M := M) r x₀
            ((continuousMultilinearMapBasis
              (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper) y))
          (fun b : Fin s => coordinateFrameAt (I := I) x₀ (lower b) y))
      x₀  := by sorry

omit [IsManifold I 2 M] in
theorem coordDeriv0SAt_applyInput_eq_sum {r s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (θ : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r)
    (x₀ : M) (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    coordDeriv0SAt (I := I) (fun x => X x) x₀
        (fun y : M =>
          tensorRSFieldApplyInput (𝕜 := 𝕜) (E := E) (H := H) (I := I)
            (M := M) (∞ : WithTop ℕ∞) T θ y)
        lower =
      (∑ upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E,
        coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => θ x) upper *
          coordComponentRSAt (I := I) (T x₀) upper lower) +
      (∑ upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E,
        coordComponent0SAt (I := I) (θ x₀) upper *
          coordDerivRSAt (I := I) (fun x => X x) x₀ (fun x => T x) upper lower)  := by sorry

end DifferentialGeometry.Tensor.Coordinates

