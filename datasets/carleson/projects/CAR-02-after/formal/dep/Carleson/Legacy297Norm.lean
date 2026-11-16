import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
noncomputable section
open scoped ENNReal NNReal
namespace MeasureTheory
variable {α ε : Type*} [MeasurableSpace α] [ENorm ε]
def legacy297Norm (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if p = 0 then 0 else if p = ∞ then eLpNormEssSup f μ else eLpNorm' f p.toReal μ
@[simp] theorem legacy297Norm_exponent_zero (f : α → ε) (μ : Measure α) : legacy297Norm f 0 μ = 0 := by simp [legacy297Norm]
@[simp] theorem legacy297Norm_exponent_top (f : α → ε) (μ : Measure α) : legacy297Norm f ∞ μ = eLpNormEssSup f μ := by simp [legacy297Norm]
theorem legacy297Norm_eq_eLpNorm' {f : α → ε} {p : ℝ≥0∞} {μ : Measure α} (h0 : p ≠ 0) (ht : p ≠ ∞) :
    legacy297Norm f p μ = eLpNorm' f p.toReal μ := by simp [legacy297Norm, h0, ht]
theorem legacy297Norm_nnreal_eq_eLpNorm' {f : α → ε} {p : ℝ≥0} {μ : Measure α} (h0 : p ≠ 0) :
    legacy297Norm f p μ = eLpNorm' f p μ := by simp [legacy297Norm, h0]
variable [TopologicalSpace ε]
theorem legacy297Norm_eq_current {f : α → ε} {p : ℝ≥0∞} {μ : Measure α} (hf : AEStronglyMeasurable f μ) :
    legacy297Norm f p μ = eLpNorm f p μ := by simp [legacy297Norm, eLpNorm, hf]
def Legacy297MemLp (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  AEStronglyMeasurable f μ ∧ legacy297Norm f p μ < ∞
theorem legacy297MemLp_iff {f : α → ε} {p : ℝ≥0∞} {μ : Measure α} :
    Legacy297MemLp f p μ ↔ MemLp f p μ := by
  constructor
  · intro h
    change eLpNorm f p μ < ∞
    rw [← legacy297Norm_eq_current h.1]
    exact h.2
  · intro h
    exact ⟨h.aestronglyMeasurable, by simpa [legacy297Norm_eq_current h.aestronglyMeasurable] using (show eLpNorm f p μ < ∞ from h)⟩
end MeasureTheory
