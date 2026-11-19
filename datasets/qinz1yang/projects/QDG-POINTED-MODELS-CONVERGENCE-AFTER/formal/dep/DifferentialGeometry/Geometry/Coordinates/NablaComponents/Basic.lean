import dep.DifferentialGeometry.Geometry.Coordinates.Connection.Coefficients
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Basic
import dep.DifferentialGeometry.Bundle.TangentSpace

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


def coordDeriv0SAt {s : ℕ}
    (X : (x : M) -> TangentSpace I x) (x₀ : M)
    (α : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) s x)
    (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  mvfderiv (I := I)
    (fun y : M => α y (fun a => coordinateFrameAt (I := I) x₀ (slots a) y))
    x₀ (X x₀)


def modelDeriv0SAt {s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M)
    (α : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) s x)
    (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  let X' : E → E := fun z =>
    tangentSpaceModelContinuousLinearEquiv z
      (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
        (fun x => X x) (Set.range I) z)
  let α' : E -> ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜 :=
    fun y => tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) s x₀ α y
  fderivWithin 𝕜 α'
    (((extChartAt I x₀).symm ⁻¹' Set.univ) ∩ Set.range I)
    (extChartAt I x₀ x₀) (X' (extChartAt I x₀ x₀))
    (fun a => (Module.finBasis 𝕜 E) (slots a))

def ModelDerivEqCoordDeriv0SAt {s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M)
    (α : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) s x) : Prop :=
  forall slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E,
    modelDeriv0SAt (I := I) X x₀ α slots =
      coordDeriv0SAt (I := I) (fun x => X x) x₀ α slots

omit [IsManifold I 2 M] in
omit [CompleteSpace 𝕜] in
theorem tensor0SModelAt_coordComponent0SAt {s : ℕ} (x₀ : M)
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x₀)
    (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ x₀ A (fun a => (Module.finBasis 𝕜 E) (slots a)) =
      coordComponent0SAt (I := I) A slots  := by sorry

omit [IsManifold I 2 M] in
omit [CompleteSpace 𝕜] in
private theorem model_component_eq_coord_component_comp_eventually {s : ℕ}
    (x₀ : M)
    (α : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) s x)
    (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    (fun y : E =>
        tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s x₀ α y (fun a => (Module.finBasis 𝕜 E) (slots a))) =ᶠ[
      𝓝[Set.range I] (extChartAt I x₀ x₀)]
    (fun y : E =>
        α ((extChartAt I x₀).symm y)
          (fun a => coordinateFrameAt (I := I) x₀ (slots a)
            ((extChartAt I x₀).symm y)))  := by sorry

omit [IsManifold I 2 M] in
omit [CompleteSpace 𝕜] in
theorem modelDeriv_eq_coordDeriv0SAt {s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x)  := by sorry

theorem nabla0S_model_coordFrame_slots {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponent0SAt (I := I)
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s cov X α x₀)
        slots =
      modelDeriv0SAt (I := I) X x₀ (fun x => α x) slots -
        ∑ a : Fin s, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) (slots a) k *
            coordComponent0SAt (I := I) (α x₀) (Function.update slots a k)  := by sorry

theorem nabla0S_coordFrame_slots {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponent0SAt (I := I)
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s cov X α x₀)
        slots =
      coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x) slots -
        ∑ a : Fin s, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) (slots a) k *
            coordComponent0SAt (I := I) (α x₀) (Function.update slots a k)  := by sorry

theorem nabla0S_coordFrame_slots_of_smooth {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponent0SAt (I := I)
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s cov X α x₀)
        slots =
      coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x) slots -
        ∑ a : Fin s, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) (slots a) k *
            coordComponent0SAt (I := I) (α x₀) (Function.update slots a k)  := by sorry

end DifferentialGeometry.Tensor.Coordinates

