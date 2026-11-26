import Mathlib.Data.Finset.Pairwise
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Kernel.IndepFun
import Mathlib.Tactic
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Finiteness
import Mathlib.Util.Notation3
import dep.LegacyMap
import dep.PFR.ForMathlib.FiniteRange.Defs
import dep.PFR.Mathlib.MeasureTheory.Constructions.Pi
import dep.PFR.Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory

namespace PFRHistorical

noncomputable def CondIndepFun {Ω α β γ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (f : Ω → α) (g : Ω → β) (h : Ω → γ) (μ : Measure Ω) : Prop :=
  ∀ᵐ z ∂ (PFRHistorical.map h μ), IndepFun f g (μ[|h ← z])

end PFRHistorical

namespace ProbabilityTheory

universe u

variable {Ω : Type*} {α β : Type u} [MeasurableSpace Ω] [MeasurableSpace α]
  [MeasurableSpace β] [MeasurableSingletonClass β]

variable [Fintype β]

lemma condIndep_copies (X : Ω → α) (Y : Ω → β) (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (X₁ X₂ : Ω' → α) (Y' : Ω' → β) (ν : Measure Ω'),
      IsProbabilityMeasure ν ∧ Measurable X₁ ∧ Measurable X₂ ∧ Measurable Y' ∧
      PFRHistorical.CondIndepFun X₁ X₂ Y' ν ∧ IdentDistrib ((fun ω => (X₁ ω, Y' ω))) ((fun ω => (X ω, Y ω))) ν μ ∧
      IdentDistrib ((fun ω => (X₂ ω, Y' ω))) ((fun ω => (X ω, Y ω))) ν μ := sorry

end ProbabilityTheory
