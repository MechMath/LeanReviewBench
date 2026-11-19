import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.FixedChart.Models
import dep.DifferentialGeometry.Bundle.TangentSpace

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

section SmoothVectorFieldRSNabla

variable [IsManifold I 1 M] [IsManifold I (n + 1) M]

noncomputable def fixedChartNabla0SModel (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (x₀ : M) [IsManifold I 2 M] (y : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  covariantDerivTensor0SModelWithin (𝕜 := 𝕜) (E := E) s
    (fun z => tangentSpaceModelContinuousLinearEquiv z
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (range I) z))
    (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
    (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) s x₀ (fun x => α x))
    (range I) y

omit [IsManifold I n M] [IsManifold I (n + 1) M] in
theorem fixedChartNabla0SModel_apply_slots (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (x₀ : M) [IsManifold I 2 M] (y : E) (slots : Fin s → E) :
    fixedChartNabla0SModel (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (n := n) s cov X α x₀ y slots =
      fderivWithin 𝕜
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) s x₀ (fun x => α x))
        (range I) y
        (tangentSpaceModelContinuousLinearEquiv y
          (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (range I) y))
        slots -
      ∑ a : Fin s,
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) s x₀ (fun x => α x)) y
          (Function.update slots a
            ((connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov
              (fun x => X x) x₀ y) (slots a)))  := by sorry

omit [IsManifold I n M] [IsManifold I (n + 1) M] in
theorem fixedChartNabla0SModel_apply_slots_of_mem (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (x₀ : M) [IsManifold I 2 M] {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (slots : Fin s → E) :
    fixedChartNabla0SModel (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (n := n) s cov X α x₀ y slots =
      fderivWithin 𝕜
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) s x₀ (fun x => α x))
        (range I) y
        (tangentSpaceModelContinuousLinearEquiv y
          (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (range I) y))
        slots -
      ∑ a : Fin s,
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) s x₀ (fun x => α x)) y
          (Function.update slots a
            ((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearMapAt
              𝕜 ((extChartAt I x₀).symm y)
                ((cov (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (slots a))
                ((extChartAt I x₀).symm y))
                (X ((extChartAt I x₀).symm y)))))  := by sorry

omit [IsManifold I n M] in
theorem fixedChartNabla0SModel_contDiffWithinAt (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov n)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (x₀ : M) [IsManifold I 2 M] [IsManifold I (n + 1 + 1) M]
    (hmn : n + 1 ≤ n) :
    ContDiffWithinAt 𝕜 n
      (fixedChartNabla0SModel (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (n := n) s cov X α x₀)
      (range I) (extChartAt I x₀ x₀)  := by sorry

end SmoothVectorFieldRSNabla

end

end TensorLieDeriv
end DifferentialGeometry

