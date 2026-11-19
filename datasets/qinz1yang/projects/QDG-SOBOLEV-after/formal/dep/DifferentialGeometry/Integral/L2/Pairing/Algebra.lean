import dep.DifferentialGeometry.Integral.L2.Pairing.Defs



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

theorem tensorL2Inner_symm
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : M → TensorRSModel r s ℝ E) :
    tensorL2Inner (I := I) (M := M) g r s S T =
      tensorL2Inner (I := I) (M := M) g r s T S  := by sorry

set_option linter.unusedSectionVars false in

theorem tensorL2Inner_add_left
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ T : M → TensorRSModel r s ℝ E)
    (h₁ : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S₁ x) (T x))
      (riemannianVolumeMeasure (I := I) (M := M) g))
    (h₂ : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S₂ x) (T x))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    tensorL2Inner (I := I) (M := M) g r s (S₁ + S₂) T =
      tensorL2Inner (I := I) (M := M) g r s S₁ T +
        tensorL2Inner (I := I) (M := M) g r s S₂ T  := by sorry

set_option linter.unusedSectionVars false in

theorem tensorL2Inner_add_right
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T₁ T₂ : M → TensorRSModel r s ℝ E)
    (h₁ : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T₁ x))
      (riemannianVolumeMeasure (I := I) (M := M) g))
    (h₂ : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T₂ x))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    tensorL2Inner (I := I) (M := M) g r s S (T₁ + T₂) =
      tensorL2Inner (I := I) (M := M) g r s S T₁ +
        tensorL2Inner (I := I) (M := M) g r s S T₂  := by sorry

set_option linter.unusedSectionVars false in

theorem tensorL2Inner_smul_left
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S T : M → TensorRSModel r s ℝ E) :
    tensorL2Inner (I := I) (M := M) g r s (c • S) T =
      c * tensorL2Inner (I := I) (M := M) g r s S T  := by sorry

set_option linter.unusedSectionVars false in

theorem tensorL2Inner_smul_right
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S T : M → TensorRSModel r s ℝ E) :
    tensorL2Inner (I := I) (M := M) g r s S (c • T) =
      c * tensorL2Inner (I := I) (M := M) g r s S T  := by sorry

set_option linter.unusedSectionVars false in

theorem tensorL2Inner_zero_left
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : M → TensorRSModel r s ℝ E) :
    tensorL2Inner (I := I) (M := M) g r s
      (fun _ : M => (0 : TensorRSModel r s ℝ E)) T = 0  := by sorry

set_option linter.unusedSectionVars false in

theorem tensorL2Inner_zero_right
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : M → TensorRSModel r s ℝ E) :
    tensorL2Inner (I := I) (M := M) g r s S
      (fun _ : M => (0 : TensorRSModel r s ℝ E)) = 0  := by sorry

set_option linter.unusedSectionVars false in

theorem tensorL2Inner_nonneg
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : M → TensorRSModel r s ℝ E) :
    0 ≤ tensorL2Inner (I := I) (M := M) g r s S S  := by sorry

set_option linter.unusedSectionVars false in

theorem MemL2.integrable_inner_of_aestronglyMeasurable
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {S T : M → TensorRSModel r s ℝ E}
    (hS : MemL2 (I := I) (M := M) g r s S)
    (hT : MemL2 (I := I) (M := M) g r s T)
    (hST_meas : MeasureTheory.AEStronglyMeasurable
      (fun x => tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    MeasureTheory.Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
      (riemannianVolumeMeasure (I := I) (M := M) g)  := by sorry

set_option linter.unusedSectionVars false in

theorem MemL2.add
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {S T : M → TensorRSModel r s ℝ E}
    (hS : MemL2 (I := I) (M := M) g r s S)
    (hT : MemL2 (I := I) (M := M) g r s T)
    (hST_meas : MeasureTheory.AEStronglyMeasurable
      (fun x => tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    MemL2 (I := I) (M := M) g r s (S + T)  := by sorry

set_option linter.unusedSectionVars false in

theorem MemL2.smul
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (c : ℝ) {S : M → TensorRSModel r s ℝ E}
    (hS : MemL2 (I := I) (M := M) g r s S) :
    MemL2 (I := I) (M := M) g r s (c • S)  := by sorry

end L2
end Integral
end DifferentialGeometry

end
