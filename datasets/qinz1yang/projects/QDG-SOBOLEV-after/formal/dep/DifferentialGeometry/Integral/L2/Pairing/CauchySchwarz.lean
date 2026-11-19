import dep.DifferentialGeometry.Integral.L2.Pairing.Algebra



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

set_option linter.unusedSectionVars false in

theorem tensorL2Inner_sq_le_mul
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : M → TensorRSModel r s ℝ E)
    (hSS : MemL2 (I := I) (M := M) g r s S)
    (hTT : MemL2 (I := I) (M := M) g r s T)
    (hST : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    (tensorL2Inner (I := I) (M := M) g r s S T) ^ 2 ≤
      tensorL2Inner (I := I) (M := M) g r s S S *
        tensorL2Inner (I := I) (M := M) g r s T T  := by sorry

set_option linter.unusedSectionVars false in

theorem abs_tensorL2Inner_le
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : M → TensorRSModel r s ℝ E)
    (hSS : MemL2 (I := I) (M := M) g r s S)
    (hTT : MemL2 (I := I) (M := M) g r s T)
    (hST : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    |tensorL2Inner (I := I) (M := M) g r s S T| ≤
      tensorL2Norm (I := I) (M := M) g r s S *
        tensorL2Norm (I := I) (M := M) g r s T  := by sorry

set_option linter.unusedSectionVars false in

theorem tensorL2Norm_add_le
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : M → TensorRSModel r s ℝ E)
    (hS : MemL2 (I := I) (M := M) g r s S)
    (hT : MemL2 (I := I) (M := M) g r s T)
    (hST : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    tensorL2Norm (I := I) (M := M) g r s (S + T) ≤
      tensorL2Norm (I := I) (M := M) g r s S +
        tensorL2Norm (I := I) (M := M) g r s T  := by sorry

end L2
end Integral
end DifferentialGeometry

end
