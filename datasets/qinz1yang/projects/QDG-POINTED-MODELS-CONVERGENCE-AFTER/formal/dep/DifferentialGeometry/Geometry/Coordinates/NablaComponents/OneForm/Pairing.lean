import dep.DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.Basic

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
theorem oneForm_pair_coordFrame_eventually
    (Z : (x : M) -> TangentSpace I x)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) :
    (fun y : M => α y (fun _ : Fin 1 => Z y)) =ᶠ[𝓝 x₀]
      (fun y : M =>
        ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y) *
            α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y))  := by sorry

omit [IsManifold I 2 M] in
omit [CompleteSpace 𝕜] in
theorem oneForm_pair_coordFrame_product_rule
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Z : (x : M) -> TangentSpace I x)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (z dz : CoordinateIdx (𝕜 := 𝕜) E -> 𝕜)
    (hz : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      z j = (coordinateFrameAtToBasis (I := I) x₀).coord j (Z x₀))
    (hdz : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      dz j =
        mvfderiv (I := I)
          (fun y : M =>
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y))
          x₀ (X x₀))
    (hdiff_z : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun y : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀)
    (hdiff_α : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun y : M => α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)) x₀) :
    mvfderiv (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) =
      ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
        (dz j * coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) +
          z j *
            coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x)
              (fun _ : Fin 1 => j))  := by sorry

end DifferentialGeometry.Tensor.Coordinates

