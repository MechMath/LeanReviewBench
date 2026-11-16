import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

noncomputable section

open ENNReal NNReal Function Set

variable {α α' E E₁ E₂ F : Type*} [ENorm F]

lemma ENNReal.Legacy212_ofReal_norm [SeminormedAddGroup E] (x : E) : .ofReal ‖x‖ = ‖x‖ₑ := by
  exact _root_.ofReal_norm x

lemma Legacy212_enorm_toReal_le {x : ℝ≥0∞} : ‖x.toReal‖ₑ ≤ x := by simp [← Legacy212_ofReal_norm, ofReal_toReal_le]

@[simp] lemma Legacy212_enorm_toReal {x : ℝ≥0∞} (hx : x ≠ ⊤) : ‖x.toReal‖ₑ = x := by
  simpa only [← _root_.ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using ENNReal.ofReal_toReal hx

/-- A type `E` equipped with a continuous map `‖·‖ₑ : E → ℝ≥0∞`.
Note: do we want to unbundle this (at least separate out `TopologicalSpace E`?)
Note: not sure if this is the "right" class to add to Mathlib. -/
class Legacy212_ContinuousENorm (E : Type*) extends ENorm E, TopologicalSpace E where
  Legacy212_continuous_enorm : Continuous enorm
  -- the topology is somehow defined by the enorm.

/-- An enormed monoid is an additive monoid endowed with a continuous enorm.
Note: not sure if this is the "right" class to add to Mathlib. -/
class Legacy212_ENormedAddMonoid (E : Type*) extends Legacy212_ContinuousENorm E, AddMonoid E where
  Legacy212_enorm_eq_zero : ∀ x : E, ‖x‖ₑ = 0 ↔ x = 0
  -- Legacy212_enorm_neg : ∀ x y : E, x + y = 0 → ‖x‖ₑ = ‖y‖ₑ -- this is a silly way to write this
  Legacy212_enorm_add_le : ∀ x y : E, ‖x + y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ

/-- An enormed monoid is an additive monoid endowed with a continuous enorm.
Note: not sure if this is the "right" class to add to Mathlib. -/
class Legacy212_ENormedAddCommMonoid (E : Type*) extends Legacy212_ENormedAddMonoid E, AddCommMonoid E where

/-- An enormed space is an additive monoid endowed with a continuous enorm.
Note: not sure if this is the "right" class to add to Mathlib. -/
class Legacy212_ENormedSpace (E : Type*) extends Legacy212_ENormedAddCommMonoid E, Module ℝ≥0 E where
  Legacy212_enorm_smul : ∀ (c : ℝ≥0) (x : E), ‖c • x‖ₑ = c • ‖x‖ₑ

export Legacy212_ENormedAddMonoid (Legacy212_enorm_eq_zero Legacy212_enorm_add_le)
export Legacy212_ENormedSpace (Legacy212_enorm_smul)
attribute [simp] Legacy212_enorm_eq_zero Legacy212_enorm_smul

@[simp] lemma Legacy212_enorm_zero {ε} [Legacy212_ENormedAddMonoid ε] : ‖(0 : ε)‖ₑ = 0 := by simp

instance : Legacy212_ENormedSpace ℝ≥0∞ where
  toModule := inferInstance
  enorm := id
  Legacy212_enorm_eq_zero := by simp
  -- Legacy212_enorm_neg := by simp
  Legacy212_enorm_add_le := by simp
  add_comm := by simp [add_comm]
  Legacy212_continuous_enorm := continuous_id
  Legacy212_enorm_smul := by simp

instance [SeminormedAddGroup E] : Legacy212_ContinuousENorm E where
  Legacy212_continuous_enorm := ENNReal.continuous_coe.comp continuous_nnnorm

instance [NormedAddGroup E] : Legacy212_ENormedAddMonoid E where
  Legacy212_enorm_eq_zero := by simp [enorm_eq_nnnorm]
  -- Legacy212_enorm_neg := by
  --   simp (config := {contextual := true}) [← eq_neg_iff_add_eq_zero, enorm_eq_nnnorm]
  Legacy212_enorm_add_le := by simp [enorm_eq_nnnorm, ← ENNReal.coe_add, nnnorm_add_le]

@[simp] lemma Legacy212_enorm_neg [NormedAddGroup E] (x : E) : ‖-x‖ₑ = ‖x‖ₑ := by
  simp_rw [enorm_eq_nnnorm, nnnorm_neg]

instance [NormedAddCommGroup E] : Legacy212_ENormedAddCommMonoid E where
  add_comm := by simp [add_comm]

instance [NormedAddCommGroup E] [NormedSpace ℝ E] : Legacy212_ENormedSpace E where
  Legacy212_enorm_smul := by simp_rw [enorm_eq_nnnorm, ENNReal.smul_def, NNReal.smul_def, nnnorm_smul]; simp

namespace MeasureTheory
section Legacy212_ContinuousENorm
variable {α E : Type*} {m : MeasurableSpace α} [Legacy212_ContinuousENorm E] {μ : Measure α}

export Legacy212_ContinuousENorm (Legacy212_continuous_enorm)

protected theorem Continuous.enorm {X : Type*} [TopologicalSpace X] {f : X → E}
    (hf : Continuous f) : Continuous (fun x => (‖f x‖ₑ)) :=
  Legacy212_continuous_enorm.comp hf

theorem Legacy212_measurable_enorm [MeasurableSpace E] [OpensMeasurableSpace E] :
    Measurable (fun a : E => (‖a‖ₑ)) :=
  Legacy212_continuous_enorm.measurable

protected theorem AEMeasurable.enorm [MeasurableSpace E] [OpensMeasurableSpace E] {f : α → E}
    (hf : AEMeasurable f μ) : AEMeasurable (fun a => (‖f a‖ₑ)) μ :=
  Legacy212_measurable_enorm.comp_aemeasurable hf

protected theorem AEStronglyMeasurable.legacy212_enorm {f : α → E}
    (hf : AEStronglyMeasurable f μ) : AEMeasurable (fun a => (‖f a‖ₑ)) μ :=
  Legacy212_continuous_enorm.comp_aestronglyMeasurable hf |>.aemeasurable

end Legacy212_ContinuousENorm

end MeasureTheory
