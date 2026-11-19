import dep.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Algebra.Product
import dep.DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Coordinate
import dep.DifferentialGeometry.Geometry.Coordinates.NablaComponents.Tensor0S
import dep.DifferentialGeometry.Geometry.Coordinates.NablaComponents.TwoTensor

set_option autoImplicit false

namespace DifferentialGeometry
namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem totalNabla0SRealizes_eval_point_vector_smooth_slots
    [T2Space M]
    {s : Nat} {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaA : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov A nablaA)
    {x : M} (W : TangentSpace I x)
    (V : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) :
    nablaA x (Fin.cons W (fun q : Fin s => V q x)) =
      mvfderiv (I := I)
        (fun y : M => A y (fun q : Fin s => V q y)) x W -
      ∑ q : Fin s,
        A x
          (Function.update (fun r : Fin s => V r x) q
            ((cov (fun y : M => V q y) x) W))  := by sorry

theorem cotangentSharp_cov_eq_sharp_curry_of_mdiffAt
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    (alpha : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (nablaAlpha : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (hAlpha : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 1 cov alpha nablaAlpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M)
    (hSharp : MDiffAt
      (T% (fun y : M => cotangentSharp (I := I) g y (alpha y))) x) :
    cov (fun y : M => cotangentSharp (I := I) g y (alpha y)) x (X x) =
      cotangentSharp (I := I) g x
        (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x
          (nablaAlpha x) (X x))  := by sorry

private theorem cotangentInner_metricCompatible_mvfderiv_of_sharp_mdiffAt
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    (alpha beta : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1)
    (nablaAlpha nablaBeta :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2)
    (hAlpha : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 1 cov alpha nablaAlpha)
    (hBeta : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 1 cov beta nablaBeta)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M)
    (hSharpAlpha : MDiffAt
      (T% (fun y : M => cotangentSharp (I := I) g y (alpha y))) x)
    (hSharpBeta : MDiffAt
      (T% (fun y : M => cotangentSharp (I := I) g y (beta y))) x) :
    mvfderiv (I := I)
        (fun y : M => cotangentInner (I := I) g y (alpha y) (beta y))
        x (X x) =
      cotangentInner (I := I) g x
        (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x
          (nablaAlpha x) (X x)) (beta x) +
        cotangentInner (I := I) g x (alpha x)
          (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x
            (nablaBeta x) (X x))  := by sorry

theorem inner0S_two_mdiff
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x : M) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) x  := by sorry

theorem inner0S_two_nabla
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    mvfderiv (I := I)
        (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) x (X x) =
      inner0S (I := I) g x 2
        (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X A x) (B x) +
        inner0S (I := I) g x 2 (A x)
          (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X B x)  := by sorry

theorem inner0S_two_metricCompatible_mvfderiv
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (nablaA nablaB :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov A nablaA)
    (hB : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov B nablaB)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    mvfderiv (I := I)
        (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) x (X x) =
      inner0S (I := I) g x 2
        (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 2 x
          (nablaA x) (X x)) (B x) +
        inner0S (I := I) g x 2 (A x)
          (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 2 x
            (nablaB x) (X x))  := by sorry

end

end Tensor0SBundle
end DifferentialGeometry

