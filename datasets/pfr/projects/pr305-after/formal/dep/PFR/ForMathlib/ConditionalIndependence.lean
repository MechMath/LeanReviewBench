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
public import dep.PFR.Mathlib.Probability.IdentDistrib
public import dep.PFR.Mathlib.Probability.Independence.Basic

@[expose] public section

open MeasureTheory Measure Set

open scoped ENNReal

namespace ProbabilityTheory

section

variable {Ω α β : Type*} {_ : MeasurableSpace Ω} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
  {μ : Measure Ω} {A : Ω → α} {B : Ω → β}

/-- If `A` is independent of `B`, then they remain independent when conditioning on an event
of the form `A ∈ s ∩ B ∈ t` of positive probability. -/
lemma IndepFun.cond (hi : IndepFun A B μ) {s : Set α} {t : Set β}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hA : Measurable A) (hB : Measurable B) :
    IndepFun A B (μ[| A ⁻¹' s ∩ B ⁻¹' t]) := sorry

end

section defs

variable {Ω Ω' α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace α]
  [MeasurableSpace β] [MeasurableSpace γ] {μ : Measure Ω} {f : Ω → α} {g : Ω → β} {h : Ω → γ}

variable [MeasurableSingletonClass γ]

end defs

section copy

universe u

variable {Ω : Type*} {α β : Type u} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β]

variable [Countable β]

open Function Set Measure

end copy

end ProbabilityTheory
