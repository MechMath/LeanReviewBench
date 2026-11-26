import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.CompleteLattice
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Order
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.DominatedConvergence
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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Topology.Sequences
import dep.LearningTheory.Rademacher.Complexity
import dep.LearningTheory.Rademacher.Defs
import dep.LearningTheory.Rademacher.Signs
import dep.LearningTheory.Rademacher.Symmetrization
import dep.LearningTheory.UniformDeviation.Defs

open Filter Topology Set MeasureTheory ProbabilityTheory

open scoped BigOperators

universe u v w x

variable {Ω : Type u} [MeasurableSpace Ω] {H : Type v} {𝒳 : Type w}

/--
A function class `F` is pointwise separable if some sequence `g` of hypotheses approximates every
hypothesis `h` pointwise along a subsequence `g ∘ u`, the same subsequence for every input.
-/
def PointwiseSeparable (F : H → 𝒳 → ℝ) : Prop :=
  ∃ g : ℕ → H, ∀ h, ∃ u : ℕ → ℕ, ∀ x,
    Tendsto (fun m ↦ F (g (u m)) x) atTop (𝓝 (F h x))

section Reduction

variable {n : ℕ}

end Reduction

namespace PointwiseSeparable

end PointwiseSeparable
