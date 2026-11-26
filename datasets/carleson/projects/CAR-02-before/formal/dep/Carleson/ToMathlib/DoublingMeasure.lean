import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.MetricSpace.Holder
import dep.Carleson.ToMathlib.CoverByBalls

open MeasureTheory Measure NNReal ENNReal Metric Filter Topology TopologicalSpace

noncomputable section

namespace MeasureTheory

/-- A doubling measure is a measure on a metric space with the condition that doubling
the radius of a ball only increases the volume by a constant factor, independent of the ball. -/
class Measure.IsDoubling {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X) (A : outParam ℝ≥0) : Prop where
  measure_ball_two_le_same : ∀ (x : X) r, μ (ball x (2 * r)) ≤ A * μ (ball x r)

export IsDoubling (measure_ball_two_le_same)

section PseudoMetric

variable {X : Type*} [PseudoMetricSpace X]

variable {A : ℝ≥0} [MeasurableSpace X] {μ : Measure X} [μ.IsDoubling A]

variable [ProperSpace X] [IsFiniteMeasureOnCompacts μ]

lemma carleson_measure_ball_ne_top (x : X) (r : ℝ) : μ (ball x r) ≠ ∞ := sorry

attribute [aesop (rule_sets := [finiteness]) safe apply] carleson_measure_ball_ne_top

section

variable {x x': X} {r r' s d : ℝ} (hs : 0 < s)

end

end PseudoMetric

section Metric

variable {X : Type*} {A : ℝ≥0} [MetricSpace X] [MeasurableSpace X]
  {μ : Measure X} [μ.IsDoubling A] [IsFiniteMeasureOnCompacts μ] [ProperSpace X]
  [Nonempty X] [IsOpenPosMeasure μ]

instance : IsUnifLocDoublingMeasure (μ : Measure X) := sorry

end Metric

section Normed

open Module ENNReal

instance InnerProductSpace.IsDoubling {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] :
    IsDoubling (volume : Measure E) (2 ^ finrank ℝ E) := sorry

end Normed

/-- A metric space with a measure and a doubling condition.
This is called a "doubling metric measure space" in the blueprint.
`A` will usually be `2 ^ a`.

This class is not Mathlib-ready code, and results moved to Mathlib should be reformulated using
a (locally) doubling measure and more minimal other classes.

Note (F): we currently assume that the space is proper, which we should probably add to the
blueprint.
Remark: `IsUnifLocDoublingMeasure` which is a weaker notion in Mathlib. -/

class DoublingMeasure (X : Type*) (A : outParam ℝ≥0) [PseudoMetricSpace X] extends
  MeasureSpace X, ProperSpace X, BorelSpace X,
  Regular (volume : Measure X), IsOpenPosMeasure (volume : Measure X),
  IsDoubling (volume : Measure X) A

variable {X : Type*} {A : ℝ≥0} [PseudoMetricSpace X] [DoublingMeasure X A]

section MetricSpace

variable {Y : Type*} [MetricSpace Y] [DoublingMeasure Y A]

end MetricSpace

open Module

instance InnerProductSpace.DoublingMeasure
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] :
    DoublingMeasure E (2 ^ finrank ℝ E) where

end MeasureTheory
