import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

noncomputable section

open ENNReal NNReal Function Set

variable {α α' E E₁ E₂ F : Type*} [ENorm F]

/-- A type `E` equipped with a continuous map `‖·‖ₑ : E → ℝ≥0∞`.
Note: do we want to unbundle this (at least separate out `TopologicalSpace E`?)
Note: not sure if this is the "right" class to add to Mathlib. -/
class Legacy212_ContinuousENorm (E : Type*) extends ENorm E, TopologicalSpace E where
  Legacy212_continuous_enorm : Continuous enorm

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

instance : Legacy212_ENormedSpace ℝ≥0∞ where
  toModule := inferInstance
  enorm := id
  Legacy212_enorm_eq_zero := sorry
  -- Legacy212_enorm_neg := by simp
  Legacy212_enorm_add_le := sorry
  add_comm := sorry
  Legacy212_continuous_enorm := continuous_id
  Legacy212_enorm_smul := sorry

instance [SeminormedAddGroup E] : Legacy212_ContinuousENorm E where
  Legacy212_continuous_enorm := ENNReal.continuous_coe.comp continuous_nnnorm

instance [NormedAddGroup E] : Legacy212_ENormedAddMonoid E where
  Legacy212_enorm_eq_zero := sorry
  -- Legacy212_enorm_neg := by
  --   simp (config := {contextual := true}) [← eq_neg_iff_add_eq_zero, enorm_eq_nnnorm]
  Legacy212_enorm_add_le := sorry

instance [NormedAddCommGroup E] : Legacy212_ENormedAddCommMonoid E where
  add_comm := sorry

instance [NormedAddCommGroup E] [NormedSpace ℝ E] : Legacy212_ENormedSpace E where
  Legacy212_enorm_smul := sorry

namespace MeasureTheory

section Legacy212_ContinuousENorm

variable {α E : Type*} {m : MeasurableSpace α} [Legacy212_ContinuousENorm E] {μ : Measure α}

export Legacy212_ContinuousENorm (Legacy212_continuous_enorm)

protected theorem Continuous.enorm {X : Type*} [TopologicalSpace X] {f : X → E}
    (hf : Continuous f) : Continuous (fun x => (‖f x‖ₑ)) := sorry

protected theorem AEMeasurable.enorm [MeasurableSpace E] [OpensMeasurableSpace E] {f : α → E}
    (hf : AEMeasurable f μ) : AEMeasurable (fun a => (‖f a‖ₑ)) μ := sorry

end Legacy212_ContinuousENorm

end MeasureTheory
