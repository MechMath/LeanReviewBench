import dep.DifferentialGeometry.Geometry.Metric.Duality
import dep.DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Dual.Basis

set_option autoImplicit false

namespace DifferentialGeometry
namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def dualToCotangentLinear {x : M} :
    Module.Dual Real (TangentSpace I x) →ₗ[Real] Tensor0SSpace 1 I x where
  toFun := dualToCotangent (I := I)
  map_add' α β := by
    apply cotangentToDualLinear_injective (I := I) (x := x)
    ext X
    change (α + β) X = α X + β X
    rfl
  map_smul' c α := by
    apply cotangentToDualLinear_injective (I := I) (x := x)
    ext X
    change (c • α) X = c * α X
    rfl

@[simp] theorem dualToCotangentLinear_apply {x : M}
    (α : Module.Dual Real (TangentSpace I x)) :
    dualToCotangentLinear (I := I) α = dualToCotangent (I := I) α  := by sorry

noncomputable def basisInvMetric {Idx : Type*}
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (i j : Idx) : Real :=
  basis.coord j ((tangentFlatEquiv (I := I) g x).symm (basis.coord i))

theorem basisInvMetric_symm {Idx : Type*}
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    forall i j : Idx,
      basisInvMetric (I := I) g x basis i j =
        basisInvMetric (I := I) g x basis j i  := by sorry

theorem basisInvMetric_isInverse {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    MetricInverseInBasis (I := I) g x basis
      (basisInvMetric (I := I) g x basis)  := by sorry

omit [FiniteDimensional ℝ E] in
theorem MetricInverseInBasis.unique {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv₁ gInv₂ : Idx → Idx → Real)
    (h₁ : MetricInverseInBasis (I := I) g x basis gInv₁)
    (h₂ : MetricInverseInBasis (I := I) g x basis gInv₂) :
    gInv₁ = gInv₂  := by sorry

omit [FiniteDimensional ℝ E] in
theorem MetricInverseInBasis.symmetric {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv) :
    forall i j : Idx, gInv i j = gInv j i  := by sorry

omit [FiniteDimensional ℝ E] in
theorem coord_eq_sum_inverseMetric_mul_inner {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (a : Idx) (V : TangentSpace I x) :
    basis.coord a V =
      ∑ k : Idx, gInv a k * g.inner x (basis k) V  := by sorry

theorem cotangentSharp_inner_eval
    (g : SmoothRiemannianMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) (X : TangentSpace I x) :
    g.inner x (cotangentSharp (I := I) g x α) X =
      α (fun _ : Fin 1 => X)  := by sorry

theorem cotangentSharp_dualToCotangent_tangentFlat
    (g : SmoothRiemannianMetric I M) (x : M) (X : TangentSpace I x) :
    cotangentSharp (I := I) g x
      (dualToCotangent (I := I) (tangentFlatLinear (I := I) g x X)) = X  := by sorry

theorem cotangentInner_dualToCotangent_tangentFlat
    (g : SmoothRiemannianMetric I M) (x : M) (X Y : TangentSpace I x) :
    cotangentInner (I := I) g x
      (dualToCotangent (I := I) (tangentFlatLinear (I := I) g x X))
      (dualToCotangent (I := I) (tangentFlatLinear (I := I) g x Y)) =
        g.inner x X Y  := by sorry

end

end Tensor0SBundle
end DifferentialGeometry

namespace DifferentialGeometry

noncomputable section

open Tensor0SBundle
open Geometry.Operator (metricSharp metricSharp_def inner_metricSharp)
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def inverseMetricSharpFib (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 1 I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun α => metricSharp (I := I) g x (cotangentToDualLinear (I := I) (x := x) α)
      map_add' := fun α β => by
        rw [map_add (cotangentToDualLinear (I := I) (x := x))]
        rw [metricSharp_def, metricSharp_def, metricSharp_def, map_add]
      map_smul' := fun c α => by
        rw [map_smul (cotangentToDualLinear (I := I) (x := x))]
        rw [metricSharp_def, metricSharp_def, map_smul]; rfl }
@[simp] lemma inverseMetricSharpFib_apply (g : SmoothRiemannianMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) :
    inverseMetricSharpFib (I := I) g x α =
      metricSharp (I := I) g x (cotangentToDualLinear (I := I) (x := x) α)  := by sorry

lemma inverseMetricSharpFib_inner (g : SmoothRiemannianMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) (w : TangentSpace I x) :
    g.inner x (inverseMetricSharpFib (I := I) g x α) w =
      cotangentToDualLinear (I := I) (x := x) α w  := by sorry

lemma inverseMetricSharpFib_zero (g : SmoothRiemannianMetric I M) (x : M) :
    inverseMetricSharpFib (I := I) g x 0 = 0  := by sorry

lemma inverseMetricSharpFib_ne_zero_of_ne_zero (g : SmoothRiemannianMetric I M) (x : M)
    {α : Tensor0SSpace 1 I x} (hα : α ≠ 0) :
    inverseMetricSharpFib (I := I) g x α ≠ 0  := by sorry

def cometricBilin (g : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) : ℝ :=
  g.inner x (inverseMetricSharpFib (I := I) g x α) (inverseMetricSharpFib (I := I) g x β)
lemma cometricBilin_eq_inner_sharp (g : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    cometricBilin (I := I) g x α β =
      g.inner x (inverseMetricSharpFib (I := I) g x α)
        (inverseMetricSharpFib (I := I) g x β)  := by sorry

lemma cometricBilin_eq_dual_sharp (g : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    cometricBilin (I := I) g x α β =
      cotangentToDualLinear (I := I) (x := x) α (inverseMetricSharpFib (I := I) g x β)  := by sorry

lemma cometricBilin_symm (g : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    cometricBilin (I := I) g x α β = cometricBilin (I := I) g x β α  := by sorry

lemma cometricBilin_self_nonneg (g : SmoothRiemannianMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) :
    0 ≤ cometricBilin (I := I) g x α α  := by sorry

lemma cometricBilin_self_pos (g : SmoothRiemannianMetric I M) (x : M)
    {α : Tensor0SSpace 1 I x} (hα : α ≠ 0) :
    0 < cometricBilin (I := I) g x α α  := by sorry

end

end DifferentialGeometry

