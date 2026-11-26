import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.CompleteLattice
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Order
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Tilted
import Mathlib.Probability.Notation
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.Cases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Sequences
import dep.LearningTheory.Rademacher.Complexity
import dep.LearningTheory.Rademacher.Defs
import dep.LearningTheory.Rademacher.PointwiseSeparable
import dep.LearningTheory.Rademacher.Signs
import dep.LearningTheory.Rademacher.Symmetrization
import dep.LearningTheory.UniformDeviation.BoundedDifference
import dep.LearningTheory.UniformDeviation.Defs
import dep.Probability.Concentration.McDiarmid

section

universe u v w

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal

variable {n : ℕ}

variable {Ω : Type u} [MeasurableSpace Ω] {ι : Type v} {𝒳 : Type w}

variable {μ : Measure Ω} {f : ι → 𝒳 → ℝ}

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

variable {H : Type v}

/-- (Main Theorem) Optimized pointwise-separable tail bound with `t = 1 / (2 * b^2)`. -/
theorem uniform_deviation_tail_bound_pointwiseSeparable_of_pos
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty H] [IsProbabilityMeasure μ]
    (F : H → 𝒳 → ℝ) (hF_meas : ∀ h, Measurable (F h))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b : ℝ} (hb : 0 < b) (hF_bound : ∀ h x, |F h x| ≤ b)
    (hF_ps : PointwiseSeparable F)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ (fun ω ↦ 2 * rademacherComplexity n F μ X + ε ≤ uniformDeviation n F μ X (X ∘ ω))).toReal ≤
      (- ε ^ 2 * n / (2 * b ^ 2)).exp := sorry

end
