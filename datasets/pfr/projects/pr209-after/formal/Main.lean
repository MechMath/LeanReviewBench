import dep.PFR.ForMathlib.ConditionalIndependence
import dep.LegacyMap
open MeasureTheory ProbabilityTheory
namespace PFRHistorical
noncomputable def CondIndepFun {Ω α β γ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (f : Ω → α) (g : Ω → β) (h : Ω → γ) (μ : Measure Ω) : Prop :=
  ∀ᵐ z ∂ (PFRHistorical.map h μ), IndepFun f g (μ[|h ← z])
theorem condIndep_eq_modern {Ω α β γ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (f : Ω → α) (g : Ω → β) (h : Ω → γ) (μ : Measure Ω) (hh : Measurable h) :
    CondIndepFun f g h μ ↔ ProbabilityTheory.CondIndepFun f g h μ := by
  simp [CondIndepFun, ProbabilityTheory.CondIndepFun, PFRHistorical.map_eq_modern hh.aemeasurable]
end PFRHistorical
namespace ProbabilityTheory
universe u
variable {Ω : Type*} {α β : Type u} [MeasurableSpace Ω] [MeasurableSpace α]
  [MeasurableSpace β] [MeasurableSingletonClass β]
variable [Countable β]
lemma condIndep_copies (X : Ω → α) (Y : Ω → β) (hX : Measurable X) (hY : Measurable Y)
    [finY : FiniteRange Y] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (X₁ X₂ : Ω' → α) (Y' : Ω' → β) (ν : Measure Ω'),
      IsProbabilityMeasure ν ∧ Measurable X₁ ∧ Measurable X₂ ∧ Measurable Y' ∧
      PFRHistorical.CondIndepFun X₁ X₂ Y' ν ∧ IdentDistrib ((fun ω => (X₁ ω, Y' ω))) ((fun ω => (X ω, Y ω))) ν μ ∧
      IdentDistrib ((fun ω => (X₂ ω, Y' ω))) ((fun ω => (X ω, Y ω))) ν μ := by
  obtain ⟨Ω', mΩ', X₁, X₂, Y', ν, hν, hX₁, hX₂, hY', hind, hid₁, hid₂⟩ :=
    condIndep_copies_modern X Y hX hY μ
  exact ⟨Ω', mΩ', X₁, X₂, Y', ν, hν, hX₁, hX₂, hY',
    (PFRHistorical.condIndep_eq_modern X₁ X₂ Y' ν hY').mpr hind, hid₁, hid₂⟩
end ProbabilityTheory
