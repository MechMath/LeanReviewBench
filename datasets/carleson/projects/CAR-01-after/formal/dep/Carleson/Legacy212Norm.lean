import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
noncomputable section
open scoped ENNReal NNReal
namespace MeasureTheory
variable {α ε : Type*} [MeasurableSpace α] [ENorm ε]
def legacy212Norm (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if p = 0 then 0 else if p = ∞ then eLpNormEssSup f μ else eLpNorm' f p.toReal μ
@[simp] theorem legacy212Norm_exponent_zero (f : α → ε) (μ : Measure α) : legacy212Norm f 0 μ = 0 := by simp [legacy212Norm]
@[simp] theorem legacy212Norm_exponent_top (f : α → ε) (μ : Measure α) : legacy212Norm f ∞ μ = eLpNormEssSup f μ := by simp [legacy212Norm]
theorem legacy212Norm_eq_eLpNorm' {f : α → ε} {p : ℝ≥0∞} {μ : Measure α} (h0 : p ≠ 0) (ht : p ≠ ∞) :
    legacy212Norm f p μ = eLpNorm' f p.toReal μ := by simp [legacy212Norm, h0, ht]
theorem legacy212Norm_nnreal_eq_eLpNorm' {f : α → ε} {p : ℝ≥0} {μ : Measure α} (h0 : p ≠ 0) :
    legacy212Norm f p μ = eLpNorm' f p μ := by simp [legacy212Norm, h0]
variable [TopologicalSpace ε]
theorem legacy212Norm_eq_current {f : α → ε} {p : ℝ≥0∞} {μ : Measure α} (hf : AEStronglyMeasurable f μ) :
    legacy212Norm f p μ = eLpNorm f p μ := by simp [legacy212Norm, eLpNorm, hf]
def Legacy212MemLp (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  AEStronglyMeasurable f μ ∧ legacy212Norm f p μ < ∞
theorem legacy212MemLp_iff {f : α → ε} {p : ℝ≥0∞} {μ : Measure α} :
    Legacy212MemLp f p μ ↔ MemLp f p μ := by
  constructor
  · intro h
    change eLpNorm f p μ < ∞
    rw [← legacy212Norm_eq_current h.1]
    exact h.2
  · intro h
    exact ⟨h.aestronglyMeasurable, by simpa [legacy212Norm_eq_current h.aestronglyMeasurable] using (show eLpNorm f p μ < ∞ from h)⟩
end MeasureTheory
