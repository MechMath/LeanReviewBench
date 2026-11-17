module

public import Mathlib.Data.FunLike.IsApply
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The zero measure evaluates pointwise to zero. -/
instance Measure.instIsZeroApply : IsZeroApply (Measure α) (Set α) ℝ≥0∞ := sorry

/-- A measure with total mass at most one. -/
class IsSubprobabilityMeasure (μ : Measure α) : Prop where
  /-- The total mass of a subprobability measure is at most one. -/
  measure_univ_le' : μ Set.univ ≤ 1

section

variable (μ : Measure α) [IsSubprobabilityMeasure μ]

instance (priority := 100) IsSubprobabilityMeasure.toIsFiniteMeasure : IsFiniteMeasure μ := sorry

end

instance (priority := 100) IsProbabilityMeasure.toIsSubprobabilityMeasure (μ : Measure α)
    [IsProbabilityMeasure μ] : IsSubprobabilityMeasure μ := sorry

instance : IsSubprobabilityMeasure (0 : Measure α) := sorry

instance (a : α) : IsSubprobabilityMeasure (Measure.dirac a) := sorry

/-- Independent products preserve the subprobability bound. -/
instance Measure.isSubprobabilityMeasure_prod (μ : Measure α) [IsSubprobabilityMeasure μ]
    (ν : Measure β) [IsSubprobabilityMeasure ν] : IsSubprobabilityMeasure (μ.prod ν) := sorry

/-- Pushforward preserves the subprobability bound, including the Dirac fallback for a
nonmeasurable map from a nonzero measure. -/
instance Measure.isSubprobabilityMeasure_map (μ : Measure α) [IsSubprobabilityMeasure μ]
    (f : α → β) : IsSubprobabilityMeasure (μ.map f) := sorry

end MeasureTheory
