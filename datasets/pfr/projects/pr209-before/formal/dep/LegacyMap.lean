import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

namespace PFRHistorical
open MeasureTheory
open scoped Classical

-- Historical pushforward totalization: non-a.e.-measurable functions map to zero.
noncomputable def map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (μ : Measure α) : Measure β :=
  if hf : AEMeasurable f μ then Measure.mapₗ (hf.mk f) μ else 0

@[simp] theorem map_eq_modern {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} {μ : Measure α} (hf : AEMeasurable f μ) :
    map f μ = Measure.map f μ := by
  rw [map, dite_eq_left hf, Measure.mapₗ_mk_apply_of_aemeasurable hf]

@[simp] theorem map_of_not_aemeasurable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} {μ : Measure α} (hf : ¬ AEMeasurable f μ) : map f μ = 0 := by
  simp [map, hf]
end PFRHistorical

namespace PFRHistorical
open MeasureTheory
theorem map.instProbability {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (μ : Measure α) [IsProbabilityMeasure μ] (hf : AEMeasurable f μ) :
    IsProbabilityMeasure (map f μ) := by
  rw [map_eq_modern hf]
  infer_instance
end PFRHistorical

open MeasureTheory in
@[simp] theorem PFRHistorical.sum_singleton_toReal {G : Type*} [Fintype G]
    [MeasurableSpace G] [MeasurableSingletonClass G] (ν : Measure G) [IsProbabilityMeasure ν] :
    (∑ x, (ν {x}).toReal) = 1 := by
  simpa [Measure.real] using (sum_measureReal_singleton (μ := ν) Finset.univ)
