import dep.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Defs
import dep.DifferentialGeometry.Geometry.Metric.RiemannianMetricTensor
import dep.DifferentialGeometry.Tensor.RSTensor.Coordinates.Expansion
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Basic
import dep.DifferentialGeometry.Bundle.Section
import dep.DifferentialGeometry.Bundle.PartialMfderiv.Basic
import dep.DifferentialGeometry.Analysis.Calculus.PartialDerivative.Mixed
import dep.DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative
open DifferentialGeometry.Tensor.RSTensor

set_option autoImplicit false

namespace DifferentialGeometry
namespace Tensor0SBundle

noncomputable section


open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def metricTensorField
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 := by
  let gInf : Bundle.ContMDiffRiemannianMetric I (∞ : WithTop ℕ∞) E
      (TangentSpace I : M -> Type _) :=
    { inner := Bundle.ContMDiffRiemannianMetric.inner g
      symm := g.symm
      pos := g.pos
      isVonNBounded := g.isVonNBounded
      contMDiff := g.contMDiff.of_le (by simp) }
  exact gInf.toTensor0S (I := I) (M := M) (n := (∞ : WithTop ℕ∞))

@[simp]
theorem metricTensorField_apply
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 -> TangentSpace I x) :
    metricTensorField (I := I) g x v = g.inner x (v 0) (v 1)  := by sorry

@[simp]
theorem metricTensorField_eval
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.eval (metricTensorField (I := I) g x) v = g.inner x (v 0) (v 1)  := by sorry

theorem nabla_metric_eval
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin 2 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 cov X
      (metricTensorField (I := I) g) x)
        (fun a : Fin 2 => V a x) = 0  := by sorry

theorem nabla_metric_zero
    [T2Space M] [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 cov X
      (metricTensorField (I := I) g) x = 0  := by sorry

theorem nabla_zero
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s cov X
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) s) x = 0  := by sorry

theorem zero_realizes_nabla
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _)) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) s)
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s + 1))  := by sorry

theorem zero_realizes_metric
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 cov (metricTensorField (I := I) g)
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem mvfderiv_mul_real
    {f h : M -> Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    mvfderiv (I := I) (fun y : M => f y * h y) x v =
      f x * mvfderiv (I := I) h x v +
        mvfderiv (I := I) f x v * h x  := by sorry

theorem nabla_smul_metric
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    (f : M -> Real)
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f)
    (df : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (hdf : ∀ x : M, ∀ v : TangentSpace I x,
      df x (fun _ : Fin 1 => v) = mvfderiv (I := I) f x v) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 cov
      (tensor0SFieldSmulByFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
        f hf (metricTensorField (I := I) g))
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2)
        df (metricTensorField (I := I) g))  := by sorry

noncomputable def metricDerivsZero
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g) :
    CanonicalSpatialDerivs0S (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) cov (metricTensorField (I := I) g) where
  nablaA := 0
  nabla2A := 0
  first := zero_realizes_metric (I := I) cov g hmc
  second := zero_realizes_nabla (I := I) 3 cov

@[simp]
theorem metricDerivsZero_nabla
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    (x : M) (slots : Fin 3 -> TangentSpace I x) :
    (metricDerivsZero (I := I) cov g hmc).nablaA x slots = 0  := by sorry

@[simp]
theorem metricDerivsZero_nabla2
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    (x : M) (slots : Fin 4 -> TangentSpace I x) :
    (metricDerivsZero (I := I) cov g hmc).nabla2A x slots = 0  := by sorry

end

end Tensor0SBundle
end DifferentialGeometry

