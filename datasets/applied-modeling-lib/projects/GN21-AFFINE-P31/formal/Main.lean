import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Set.Disjoint
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import dep.EconCSLib.Foundations.Probability.CTMC
import dep.GN21DriverSurgePricing.MainTheorems

open EconCSLib

open MeasureTheory

open scoped Function ProbabilityTheory Topology ENNReal

namespace GN21DriverSurgePricing

namespace PaperInterface

/--
Proposition 3.1 source-facing measurable IC endpoint: in the continuous
single-state model with affine pricing `w(τ)=mτ+a`, the paper condition
`0 <= a <= m/λ` makes accepting all positive-length trips optimal among all
measurable feasible policies.
-/
theorem proposition3_1_affine_single_state_measurable_ic
    (mu : Measure TripLength) (arrivalRate m a : ℝ)
    (A : SingleStateTripMeasureAssumptions mu)
    (hlambda : 0 < arrivalRate)
    (ha_nonneg : 0 ≤ a)
    (ha_le_wait_value : a ≤ m / arrivalRate) :
    singleStateMeasurableIncentiveCompatible
      (affineSingleStateRenewalReward mu arrivalRate m a) := sorry

end PaperInterface

end GN21DriverSurgePricing
