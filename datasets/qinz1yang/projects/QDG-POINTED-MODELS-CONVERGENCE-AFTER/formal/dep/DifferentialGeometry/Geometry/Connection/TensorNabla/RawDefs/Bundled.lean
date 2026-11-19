import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.RawDefs.MCovariant
import dep.DifferentialGeometry.Tensor.Multilinear.Bundle.Evaluation
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.InducedConnection

namespace DifferentialGeometry
namespace Tensor0SBundle

noncomputable section


open Bundle Set IsManifold ContinuousLinearMap VectorField Filter Function
    DifferentialGeometry.TensorLieDeriv
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [CompleteSpace 𝕜]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]

omit [IsManifold I ∞ M] in
theorem nabla0SFun_apply_selfChart_slots (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) (slots : Fin s → E) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α x)
      (fun a : Fin s =>
        tangentConstInChart (𝕜 := 𝕜) (I := I) x (slots a) x) =
      fixedChartNabla0SModel (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s cov X α x
        (extChartAt I x x) slots  := by sorry

end

noncomputable section RealDerivationSmoothness

open Bundle
open scoped Manifold Topology Bundle ContDiff BigOperators

variable {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace Real E₀]
variable [FiniteDimensional Real E₀]
variable {H₀ : Type*} [TopologicalSpace H₀]
variable {I₀ : ModelWithCorners Real E₀ H₀}
variable {M₀ : Type*} [TopologicalSpace M₀] [ChartedSpace H₀ M₀]
variable [IsManifold I₀ ∞ M₀]

theorem tensor0S_eval_covariantDerivative_slot_contMDiff {s : ℕ}
    (cov : CovariantDerivative I₀ E₀ (TangentSpace I₀ : M₀ → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
    (X : ContMDiffSection I₀ E₀ ∞ (TangentSpace I₀ : M₀ → Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E₀) (H := H₀) (I := I₀) (M := M₀)
      (n := ∞) s)
    (Y : Fin s → ContMDiffSection I₀ E₀ ∞ (TangentSpace I₀ : M₀ → Type _))
    (a : Fin s) :
    ContMDiff I₀ 𝓘(Real, Real) ∞
      (fun p : M₀ =>
        α p
          (Function.update (fun b : Fin s => Y b p) a
            ((cov (fun q : M₀ => Y a q) p) (X p))))  := by sorry

end RealDerivationSmoothness

end Tensor0SBundle
end DifferentialGeometry

