import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

namespace PFRHistorical

open MeasureTheory

open scoped Classical

noncomputable def map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (μ : Measure α) : Measure β :=
  if hf : AEMeasurable f μ then Measure.mapₗ (hf.mk f) μ else 0

end PFRHistorical

namespace PFRHistorical

open MeasureTheory

end PFRHistorical
