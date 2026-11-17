module

public import Mathlib.Data.Finset.Pairwise
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Kernel.IndepFun
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Finiteness
public import Mathlib.Util.Notation3
public import dep.PFR.ForMathlib.FiniteRange.Defs
public import dep.PFR.ForMathlib.Pair
public import dep.PFR.Mathlib.MeasureTheory.Constructions.Pi
public import dep.PFR.Mathlib.Probability.Independence.Basic

@[expose] public section

open MeasureTheory Measure Set

open scoped ENNReal

namespace ProbabilityTheory

section

variable {Ω α β : Type*} {_ : MeasurableSpace Ω} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
  {μ : Measure Ω} {A : Ω → α} {B : Ω → β}

end

section defs

variable {Ω Ω' α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace α]
  [MeasurableSpace β] [MeasurableSpace γ] {μ : Measure Ω} {f : Ω → α} {g : Ω → β} {h : Ω → γ}

/-- The assertion that `f` and `g` are conditionally independent relative to `h`. -/
def CondIndepFun (f : Ω → α) (g : Ω → β) (h : Ω → γ) (μ : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ z ∂ (μ.map h), IndepFun f g (μ[|h ← z])

variable [MeasurableSingletonClass γ]

end defs

section copy

universe u

variable {Ω : Type*} {α β : Type u} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β]

open Function Set Measure

/-- For `X, Y` random variables, there exist conditionally independent trials `X_1, X_2, Y'`. -/
lemma condIndep_copies (X : Ω → α) (Y : Ω → β) (hX : Measurable X) (hY : Measurable Y)
    [finY : FiniteRange Y] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (X₁ X₂ : Ω' → α) (Y' : Ω' → β) (ν : Measure Ω'),
      IsProbabilityMeasure ν ∧ Measurable X₁ ∧ Measurable X₂ ∧ Measurable Y' ∧
      CondIndepFun X₁ X₂ Y' ν ∧ IdentDistrib (⟨X₁, Y'⟩) (⟨X, Y⟩) ν μ ∧
      IdentDistrib (⟨X₂, Y'⟩) (⟨X, Y⟩) ν μ := sorry

end copy

end ProbabilityTheory
