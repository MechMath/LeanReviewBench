import Mathlib.Algebra.Order.Group.CompleteLattice
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Notation
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.Cases
import dep.LearningTheory.Rademacher.Defs
import dep.LearningTheory.Rademacher.Signs
import dep.LearningTheory.Rademacher.Symmetrization

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω] {Z : Type w}

variable {n : ℕ} {ι : Type*} {f : ι → Z → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

end
