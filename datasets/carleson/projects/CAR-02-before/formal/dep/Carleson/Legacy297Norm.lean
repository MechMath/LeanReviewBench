import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

noncomputable section

open scoped ENNReal NNReal

namespace MeasureTheory

variable {α ε : Type*} [MeasurableSpace α] [ENorm ε]

def legacy297Norm (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if p = 0 then 0 else if p = ∞ then eLpNormEssSup f μ else eLpNorm' f p.toReal μ

variable [TopologicalSpace ε]

def Legacy297MemLp (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  AEStronglyMeasurable f μ ∧ legacy297Norm f p μ < ∞

end MeasureTheory
