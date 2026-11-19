import dep.DifferentialGeometry.Integral.L2.PointwiseInner.DualMetric
import dep.DifferentialGeometry.Integral.L2.PointwiseInner.Defs
import dep.DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Sqrt



noncomputable section

open Manifold Set Filter Bundle Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace L2

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]




theorem tensorInnerPointwise_0s_add_left
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (S₁ S₂ T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) s g x (S₁ + S₂) T =
      tensorInnerPointwise_0s (I := I) (M := M) s g x S₁ T +
        tensorInnerPointwise_0s (I := I) (M := M) s g x S₂ T  := by sorry

theorem tensorInnerPointwise_0s_add_right
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (S T₁ T₂ : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) s g x S (T₁ + T₂) =
      tensorInnerPointwise_0s (I := I) (M := M) s g x S T₁ +
        tensorInnerPointwise_0s (I := I) (M := M) s g x S T₂  := by sorry

theorem tensorInnerPointwise_0s_smul_left
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (c : ℝ) (S T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) s g x (c • S) T =
      c * tensorInnerPointwise_0s (I := I) (M := M) s g x S T  := by sorry

theorem tensorInnerPointwise_0s_smul_right
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (c : ℝ) (S T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) s g x S (c • T) =
      c * tensorInnerPointwise_0s (I := I) (M := M) s g x S T  := by sorry

theorem tensorInnerPointwise_0s_symm
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) s g x S T =
      tensorInnerPointwise_0s (I := I) (M := M) s g x T S  := by sorry

theorem tensorInnerPointwise_0s_zero_left
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) s g x 0 T = 0  := by sorry

theorem tensorInnerPointwise_0s_zero_right
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) s g x S 0 = 0  := by sorry

theorem tensorInnerPointwise_0s_zero_arity_nonneg
    (g : SmoothRiemannianMetric I M) (x : M)
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) :
    0 ≤ tensorInnerPointwise_0s (I := I) (M := M) 0 g x S S  := by sorry

theorem tensorInnerPointwise_0s_zero_arity_eq_zero_iff
    (g : SmoothRiemannianMetric I M) (x : M)
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) 0 g x S S = 0 ↔ S = 0  := by sorry

private lemma tensorInnerPointwise_0s_sum_left
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {ι : Type*} (A : Finset ι)
    (a : ι → ℝ)
    (ψ : ι → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) s g x
        (∑ i ∈ A, a i • ψ i) T =
      ∑ i ∈ A, a i *
        tensorInnerPointwise_0s (I := I) (M := M) s g x (ψ i) T  := by sorry

private lemma tensorInnerPointwise_0s_sum_right
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {ι : Type*} (A : Finset ι)
    (a : ι → ℝ)
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
    (ψ : ι → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) s g x
        S (∑ i ∈ A, a i • ψ i) =
      ∑ i ∈ A, a i *
        tensorInnerPointwise_0s (I := I) (M := M) s g x S (ψ i)  := by sorry

private lemma tensorInnerPointwise_0s_sum_sum
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {ι₁ ι₂ : Type*}
    (A : Finset ι₁) (B : Finset ι₂)
    (a : ι₁ → ℝ) (b : ι₂ → ℝ)
    (φ : ι₁ → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
    (ψ : ι₂ → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) s g x
        (∑ i ∈ A, a i • φ i) (∑ j ∈ B, b j • ψ j) =
      ∑ i ∈ A, ∑ j ∈ B,
        a i * b j *
          tensorInnerPointwise_0s (I := I) (M := M) s g x (φ i) (ψ j)  := by sorry

theorem tensorInnerPointwise_0s_nonneg
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    0 ≤ tensorInnerPointwise_0s (I := I) (M := M) s g x S S  := by sorry

theorem tensorInnerPointwise_0s_eq_zero_iff
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) s g x S S = 0 ↔ S = 0  := by sorry

theorem tensorInnerPointwise_symm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (S T : TensorRSModel r s ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g r s x S T =
      tensorInnerPointwise (I := I) (M := M) g r s x T S  := by sorry

theorem tensorInnerPointwise_add_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (S₁ S₂ T : TensorRSModel r s ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g r s x (S₁ + S₂) T =
      tensorInnerPointwise (I := I) (M := M) g r s x S₁ T +
        tensorInnerPointwise (I := I) (M := M) g r s x S₂ T  := by sorry

theorem tensorInnerPointwise_add_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (S T₁ T₂ : TensorRSModel r s ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g r s x S (T₁ + T₂) =
      tensorInnerPointwise (I := I) (M := M) g r s x S T₁ +
        tensorInnerPointwise (I := I) (M := M) g r s x S T₂  := by sorry

theorem tensorInnerPointwise_smul_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (S T : TensorRSModel r s ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g r s x (c • S) T =
      c * tensorInnerPointwise (I := I) (M := M) g r s x S T  := by sorry

theorem tensorInnerPointwise_smul_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (S T : TensorRSModel r s ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g r s x S (c • T) =
      c * tensorInnerPointwise (I := I) (M := M) g r s x S T  := by sorry

theorem tensorInnerPointwise_zero_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g r s x 0 T = 0  := by sorry

theorem tensorInnerPointwise_zero_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (S : TensorRSModel r s ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g r s x S 0 = 0  := by sorry

theorem tensorInnerPointwise_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (S : TensorRSModel r s ℝ E) :
    0 ≤ tensorInnerPointwise (I := I) (M := M) g r s x S S  := by sorry

theorem tensorInnerPointwise_eq_zero_iff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (S : TensorRSModel r s ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g r s x S S = 0 ↔ S = 0  := by sorry

theorem tensorInnerPointwise_0s_sq_le_mul
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    (tensorInnerPointwise_0s (I := I) (M := M) s g x S T) ^ 2 ≤
      tensorInnerPointwise_0s (I := I) (M := M) s g x S S *
        tensorInnerPointwise_0s (I := I) (M := M) s g x T T  := by sorry

theorem tensorInnerPointwise_sq_le_mul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (S T : TensorRSModel r s ℝ E) :
    (tensorInnerPointwise (I := I) (M := M) g r s x S T) ^ 2 ≤
      tensorInnerPointwise (I := I) (M := M) g r s x S S *
        tensorInnerPointwise (I := I) (M := M) g r s x T T  := by sorry

theorem abs_tensorInnerPointwise_le_mul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (S T : TensorRSModel r s ℝ E) :
    |tensorInnerPointwise (I := I) (M := M) g r s x S T| ≤
      tensorPointwiseNorm (I := I) (M := M) g r s x S *
        tensorPointwiseNorm (I := I) (M := M) g r s x T  := by sorry

end L2
end Integral
end DifferentialGeometry

end
