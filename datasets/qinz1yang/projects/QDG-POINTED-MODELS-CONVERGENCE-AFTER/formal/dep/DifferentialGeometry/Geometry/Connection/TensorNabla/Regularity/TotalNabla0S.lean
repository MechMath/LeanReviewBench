import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Basic
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.Regularity.Tensor0S
import dep.DifferentialGeometry.Bundle.Frame
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.BumpFunction
open DifferentialGeometry.Tensor.Multilinear

namespace DifferentialGeometry
namespace Tensor0SBundle

open Bundle Set DifferentialGeometry.TensorLieDeriv
open scoped Manifold ContDiff Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]

theorem totalNabla0S_eval_tangentConstInChart_contMDiffAt
    {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) (slots : Fin (s + 1) -> Fin (Module.finrank Real E)) :
    ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov α p)
          (fun a : Fin (s + 1) =>
            tangentConstInChart (𝕜 := Real) (I := I) x₀
              ((Module.finBasis Real E) (slots a)) p)) x₀  := by sorry

theorem totalNabla0S_regularity (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    TotalNabla0SRegular (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov α  := by sorry

noncomputable def CanonicalSpatialDerivs0S.ofSmoothConnection {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    CanonicalSpatialDerivs0S (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) cov A := by
  let hreg1 := totalNabla0S_regularity (E := E) (H := H) (I := I) (M := M)
    s cov hcov A
  let nablaA := totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) s cov A hreg1
  let hreg2 := totalNabla0S_regularity (E := E) (H := H) (I := I) (M := M)
    (s + 1) cov hcov nablaA
  refine
    { nablaA := nablaA
      nabla2A := totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) (s + 1) cov nablaA hreg2
      first := ?_
      second := ?_ }
  · exact totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) s cov A hreg1
  · exact totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) (s + 1) cov nablaA hreg2

end

end Tensor0SBundle
end DifferentialGeometry

