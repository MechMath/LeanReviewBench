module

public import Mathlib.MeasureTheory.Measure.Prod

public section

open Function

open scoped ENNReal NNReal

namespace MeasureTheory.Measure

variable {Ω α β γ : Type*} [MeasurableSpace Ω]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}

end MeasureTheory.Measure

open MeasureTheory

set_option linter.flexible false in
instance {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    [IsZeroOrProbabilityMeasure μ] {ν : Measure β} [IsZeroOrProbabilityMeasure ν] :
    IsZeroOrProbabilityMeasure (μ.prod ν) := sorry
