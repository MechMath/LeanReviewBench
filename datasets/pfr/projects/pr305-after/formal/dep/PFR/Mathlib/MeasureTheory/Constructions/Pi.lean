module

public import Mathlib.MeasureTheory.Constructions.Pi

public section

open Function Set

namespace MeasureTheory.Measure

variable {ι : Type*} {α : ι → Type*} [Fintype ι] [∀ i, MeasurableSpace (α i)]
  (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]

instance : IsProbabilityMeasure (.pi μ) := sorry

end MeasureTheory.Measure
