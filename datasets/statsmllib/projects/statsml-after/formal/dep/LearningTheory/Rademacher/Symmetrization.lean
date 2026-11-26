import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Notation
import Mathlib.Tactic.Cases
import dep.LearningTheory.Rademacher.Defs

open MeasureTheory ProbabilityTheory Real

universe u v w

variable {Z : Type w} {ι : Type v}

variable {f : ι → Z → ℝ}

variable {Ω : Type u} [MeasurableSpace Ω]

variable {X : Ω → Z}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

variable {n : ℕ}

@[simp]
theorem Signs.card (n : ℕ) : Fintype.card (Signs n) = 2^n := sorry
