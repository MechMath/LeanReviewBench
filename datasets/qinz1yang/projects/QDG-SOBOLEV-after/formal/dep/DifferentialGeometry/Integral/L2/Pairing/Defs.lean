import dep.DifferentialGeometry.Integral.Measure.Properties
import dep.DifferentialGeometry.Integral.L2.Basic
import dep.DifferentialGeometry.Integral.L2.PointwiseInner.Defs
import dep.DifferentialGeometry.Integral.L2.PointwiseInner.DualMetric
import dep.DifferentialGeometry.Integral.L2.PointwiseInner.Algebra
import dep.DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Data.Real.Sqrt



noncomputable section

open Manifold MeasureTheory Set Filter Bundle Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace L2

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]



private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩




noncomputable def tensorL2Inner
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : M → TensorRSModel r s ℝ E) : ℝ :=
  ∫ x, tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)
    ∂(riemannianVolumeMeasure (I := I) (M := M) g)




def MemL2
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : M → TensorRSModel r s ℝ E) : Prop :=
  MeasureTheory.Integrable
    (fun x => tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x))
    (riemannianVolumeMeasure (I := I) (M := M) g)

set_option linter.unusedSectionVars false in

lemma MemL2.integrable_inner_self
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {S : M → TensorRSModel r s ℝ E} (hS : MemL2 (I := I) (M := M) g r s S) :
    MeasureTheory.Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x))
      (riemannianVolumeMeasure (I := I) (M := M) g)  := by sorry

set_option linter.unusedSectionVars false in

theorem MemL2.zero
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    MemL2 (I := I) (M := M) g r s (fun _ : M => (0 : TensorRSModel r s ℝ E))  := by sorry

noncomputable def tensorL2Norm
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : M → TensorRSModel r s ℝ E) : ℝ :=
  Real.sqrt (tensorL2Inner (I := I) (M := M) g r s S S)

set_option linter.unusedSectionVars false in

lemma tensorL2Norm_def
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : M → TensorRSModel r s ℝ E) :
    tensorL2Norm (I := I) (M := M) g r s S =
      Real.sqrt (tensorL2Inner (I := I) (M := M) g r s S S)  := by sorry

set_option linter.unusedSectionVars false in

theorem tensorL2Norm_nonneg
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : M → TensorRSModel r s ℝ E) :
    0 ≤ tensorL2Norm (I := I) (M := M) g r s S  := by sorry

end L2
end Integral
end DifferentialGeometry

end
