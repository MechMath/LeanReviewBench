import Mathlib.Algebra.Order.Group.Int
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.Finiteness
import Mathlib.Topology.MetricSpace.Holder
import dep.Carleson.CoverByBalls
import dep.Carleson.Defs
import dep.Carleson.DoublingMeasure
import dep.Carleson.Legacy212Norm
import dep.Carleson.ToMathlib.ENorm
import dep.Carleson.WeakType

open MeasureTheory Set

noncomputable section

/-- The constant used in `metric_carleson`.
Has value `2 ^ (450 * a ^ 3) / (q - 1) ^ 6` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
def C1_0_2 (a : ℕ) (q : ℝ) : ℝ := 2 ^ (450 * a ^ 3) / (q - 1) ^ 6

variable {X : Type*} {a : ℕ} [MetricSpace X] [DoublingMeasure X (defaultA a : ℕ)]

variable {τ q q' : ℝ} {C : ℝ}

variable {F G : Set X}

variable {K : X → X → ℂ}

theorem metric_carleson [CompatibleFunctions ℝ X (defaultA a)]
  [IsCancellative X (defaultτ a)] [IsOneSidedKernel a K]
    (ha : 4 ≤ a) (hq : q ∈ Ioc 1 2) (hqq' : q.IsConjExponent q')
    (hF : MeasurableSet F) (hG : MeasurableSet G)
    (hT : HasBoundedStrongType (nontangentialOperator K · · |>.toReal) 2 2 volume volume (C_Ts a))
    (f : X → ℂ) (hmf : Measurable f) (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
    ∫⁻ x in G, carlesonOperator K f x ≤
    ENNReal.ofReal (C1_0_2 a q) * (volume G) ^ q'⁻¹ * (volume F) ^ q⁻¹ := sorry

end
