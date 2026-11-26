module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

@[expose] public section

open MeasureTheory

namespace Except

variable {ε α β : Type*}

/-- The coproduct measurable space on `Except ε α`. -/
instance instMeasurableSpace [mε : MeasurableSpace ε] [mα : MeasurableSpace α] :
    MeasurableSpace (Except ε α) :=
  mε.map error ⊓ mα.map ok

/-- `Except.ok` embeds the successful branch into the coproduct measurable space. -/
theorem measurableEmbedding_ok [MeasurableSpace ε] [MeasurableSpace α] :
    MeasurableEmbedding (@Except.ok ε α) := sorry

instance instDiscreteMeasurableSpace [MeasurableSpace ε] [MeasurableSpace α]
    [DiscreteMeasurableSpace ε] [DiscreteMeasurableSpace α] :
    DiscreteMeasurableSpace (Except ε α) := sorry

end Except
