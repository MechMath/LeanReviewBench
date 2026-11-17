import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import dep.Carleson.Legacy297Norm

noncomputable section

open ENNReal NNReal Function Set

variable {α α' E E₁ E₂ F : Type*} [ENorm F]

/-- An enormed space is an additive monoid endowed with a continuous enorm.
Note: not sure if this is the "right" class to add to Mathlib. -/
class ENormedSpace (E : Type*) [TopologicalSpace E] extends ENormedAddCommMonoid E, Module ℝ≥0 E where
  enorm_smul : ∀ (c : ℝ≥0) (x : E), ‖c • x‖ₑ = c • ‖x‖ₑ

export ENormedSpace (enorm_smul)

attribute [simp] ENormedSpace.enorm_smul

instance : ENormedSpace ℝ≥0∞ where
  enorm_zero := rfl
  enorm := id
  enorm_eq_zero := by simp
  -- enorm_neg := by simp
  enorm_add_le := by simp
  add_comm := by simp [add_comm]
  continuous_enorm := continuous_id
  enorm_smul := by simp
  add_smul := fun _ _ _ ↦ Module.add_smul ..
  zero_smul := by simp

instance : ENormedSpace ℝ≥0 where
  enorm_zero := rfl
  enorm := ofNNReal
  add_smul r s x := by
    simp only [id_eq, smul_eq_mul]
    ring
  zero_smul := by simp
  enorm_eq_zero := by simp
  enorm_add_le := by simp
  add_comm := by simp [add_comm]
  continuous_enorm := by fun_prop
  enorm_smul c x := by simp [ENNReal.smul_def]

instance [NormedAddCommGroup E] [NormedSpace ℝ E] : ENormedSpace E where
  enorm_smul := by simp_rw [enorm_eq_nnnorm, ENNReal.smul_def, NNReal.smul_def, nnnorm_smul]; simp

namespace MeasureTheory

section ContinuousENorm

variable {α E : Type*} {m : MeasurableSpace α} [TopologicalSpace E] [ContinuousENorm E] {μ : Measure α}

variable {ε ε' : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
  [TopologicalSpace ε'] [ContinuousENorm ε']

end ContinuousENorm

section ENormedSpace

variable {ε : Type*} [TopologicalSpace ε] [ENormedSpace ε]

instance : ContinuousConstSMul ℝ≥0 ℝ≥0∞ := sorry

open MeasureTheory

variable {ε' : Type*} [TopologicalSpace ε'] [ENormedSpace ε']

end ENormedSpace

end MeasureTheory
