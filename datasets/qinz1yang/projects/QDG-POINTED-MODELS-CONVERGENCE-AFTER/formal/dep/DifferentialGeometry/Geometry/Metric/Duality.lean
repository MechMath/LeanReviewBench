import dep.DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def metricFlatLinear (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →ₗ[ℝ] (TangentSpace I x →ₗ[ℝ] ℝ) where
  toFun v := (g.inner x v).toLinearMap
  map_add' v w := by
    ext u
    change g.inner x (v + w) u = g.inner x v u + g.inner x w u
    rw [map_add, add_apply]
  map_smul' c v := by
    ext u
    change g.inner x (c • v) u = c • g.inner x v u
    rw [map_smul, smul_apply]

omit [Module.Finite ℝ E] in
@[simp] lemma metricFlatLinear_apply (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    metricFlatLinear (I := I) g x v w = g.inner x v w  := by sorry

omit [Module.Finite ℝ E] in
lemma metricFlatLinear_injective (g : SmoothRiemannianMetric I M) (x : M) :
    Function.Injective (metricFlatLinear (I := I) g x)  := by sorry

private instance tangentSpace_finiteDimensional (x : M) :
    FiniteDimensional ℝ (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
private lemma metricFlatLinear_finrank_eq (x : M) :
    Module.finrank ℝ (TangentSpace I x) =
      Module.finrank ℝ (TangentSpace I x →ₗ[ℝ] ℝ)  := by sorry

def metricFlatMap (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x ≃ₗ[ℝ] (TangentSpace I x →ₗ[ℝ] ℝ) :=
  LinearMap.linearEquivOfInjective
    (metricFlatLinear (I := I) g x)
    (metricFlatLinear_injective (I := I) g x)
    (metricFlatLinear_finrank_eq (I := I) (M := M) x)

@[simp] lemma metricFlatMap_apply (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    metricFlatMap (I := I) g x v w = g.inner x v w  := by sorry

lemma metricFlatMap_apply_symm (g : SmoothRiemannianMetric I M) (x : M)
    (α : TangentSpace I x →ₗ[ℝ] ℝ) (w : TangentSpace I x) :
    g.inner x ((metricFlatMap (I := I) g x).symm α) w = α w  := by sorry

def metricSharp (g : SmoothRiemannianMetric I M) (x : M)
    (α : TangentSpace I x →ₗ[ℝ] ℝ) : TangentSpace I x :=
  (metricFlatMap (I := I) g x).symm α

@[simp] lemma metricSharp_def (g : SmoothRiemannianMetric I M) (x : M)
    (α : TangentSpace I x →ₗ[ℝ] ℝ) :
    metricSharp (I := I) g x α = (metricFlatMap (I := I) g x).symm α  := by sorry

lemma inner_metricSharp (g : SmoothRiemannianMetric I M) (x : M)
    (α : TangentSpace I x →ₗ[ℝ] ℝ) (w : TangentSpace I x) :
    g.inner x (metricSharp (I := I) g x α) w = α w  := by sorry

lemma inner_metricSharp_right (g : SmoothRiemannianMetric I M) (x : M)
    (α : TangentSpace I x →ₗ[ℝ] ℝ) (w : TangentSpace I x) :
    g.inner x w (metricSharp (I := I) g x α) = α w  := by sorry

end DifferentialGeometry.Geometry.Operator

end

