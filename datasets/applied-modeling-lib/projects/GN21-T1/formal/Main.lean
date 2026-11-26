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
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import dep.EconCSLib.Foundations.Probability.CTMC
import dep.GN21DriverSurgePricing.MainTheorems

open EconCSLib

open MeasureTheory

open scoped Function ProbabilityTheory Topology ENNReal

namespace GN21DriverSurgePricing

namespace PaperInterface

/-- Theorem 1: single-state threshold best response. -/
abbrev theorem1_single_state_threshold_best_response : ∀ (mu : @MeasureTheory.Measure.{0} GN21DriverSurgePricing.TripLength Real.measurableSpace) (arrivalRate : Real)
  (w : GN21DriverSurgePricing.PricingFunction)
  (hrate_measurable :
    @Measurable.{0, 0} GN21DriverSurgePricing.TripLength Real Real.measurableSpace Real.measurableSpace
      fun (tau : GN21DriverSurgePricing.TripLength) =>
      @HDiv.hDiv.{0, 0, 0} Real GN21DriverSurgePricing.TripLength Real
        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) (w tau) tau)
  (hrate_nonneg :
    ∀ (tau : GN21DriverSurgePricing.TripLength),
      @LT.lt.{0} GN21DriverSurgePricing.TripLength Real.instLT
          (@OfNat.ofNat.{0} GN21DriverSurgePricing.TripLength (nat_lit 0)
            (@Zero.toOfNat0.{0} GN21DriverSurgePricing.TripLength Real.instZero))
          tau →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@HDiv.hDiv.{0, 0, 0} Real GN21DriverSurgePricing.TripLength Real
            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) (w tau) tau))
  (hfinite_acceptAll :
    @Ne.{1} ENNReal
      (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} GN21DriverSurgePricing.TripLength Real.measurableSpace)
        (Set.{0} GN21DriverSurgePricing.TripLength) (fun (x : Set.{0} GN21DriverSurgePricing.TripLength) => ENNReal)
        (@MeasureTheory.Measure.instFunLike.{0} GN21DriverSurgePricing.TripLength Real.measurableSpace) mu
        GN21DriverSurgePricing.acceptAllPolicy)
      (@Top.top.{0} ENNReal ENNReal.instTop))
  (hw_integrable_acceptAll :
    @MeasureTheory.IntegrableOn.{0, 0} GN21DriverSurgePricing.TripLength Real Real.measurableSpace
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@SeminormedAddGroup.toContinuousENorm.{0} Real
        (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real
          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
              (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))))
      w GN21DriverSurgePricing.acceptAllPolicy mu)
  (htime_integrable_acceptAll :
    @MeasureTheory.IntegrableOn.{0, 0} GN21DriverSurgePricing.TripLength GN21DriverSurgePricing.TripLength
      Real.measurableSpace
      (@UniformSpace.toTopologicalSpace.{0} GN21DriverSurgePricing.TripLength
        (@PseudoMetricSpace.toUniformSpace.{0} GN21DriverSurgePricing.TripLength Real.pseudoMetricSpace))
      (@SeminormedAddGroup.toContinuousENorm.{0} GN21DriverSurgePricing.TripLength
        (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} GN21DriverSurgePricing.TripLength
          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} GN21DriverSurgePricing.TripLength
            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} GN21DriverSurgePricing.TripLength
              (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} GN21DriverSurgePricing.TripLength
                (@NormedCommRing.toSeminormedCommRing.{0} GN21DriverSurgePricing.TripLength Real.normedCommRing))))))
      (fun (tau : GN21DriverSurgePricing.TripLength) => tau) GN21DriverSurgePricing.acceptAllPolicy mu)
  (hlambda :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) arrivalRate)
  (hpayment_acceptAll_pos :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (GN21DriverSurgePricing.singleStateTripPayment mu w GN21DriverSurgePricing.acceptAllPolicy)),
  @Exists.{1} Real fun (c : Real) =>
    And (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c)
      (@Exists.{1} GN21DriverSurgePricing.TripPolicy fun (sigma : GN21DriverSurgePricing.TripPolicy) =>
        And (GN21DriverSurgePricing.thresholdRatePolicy w c sigma)
          (GN21DriverSurgePricing.singleStateMeasurableOptimal
            (GN21DriverSurgePricing.singleStateRenewalReward mu arrivalRate w) sigma)) := sorry

end PaperInterface

end GN21DriverSurgePricing
