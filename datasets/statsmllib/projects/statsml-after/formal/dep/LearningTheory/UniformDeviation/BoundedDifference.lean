import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.CompleteLattice
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Order
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Notation
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.Cases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Real.Lemmas
import dep.LearningTheory.Rademacher.Complexity
import dep.LearningTheory.Rademacher.Defs
import dep.LearningTheory.Rademacher.Signs
import dep.LearningTheory.Rademacher.Symmetrization
import dep.LearningTheory.UniformDeviation.Defs

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω] {𝒳 : Type w}

variable {n : ℕ} {ι : Type v} {f : ι → 𝒳 → ℝ} {μ : Measure Ω}

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

end
