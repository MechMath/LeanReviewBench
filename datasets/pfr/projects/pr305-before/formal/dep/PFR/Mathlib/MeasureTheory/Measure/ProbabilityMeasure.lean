module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

public section

open MeasureTheory ProbabilityMeasure Topology Metric Filter Set ENNReal NNReal

open scoped BoundedContinuousFunction Topology ENNReal NNReal

attribute [fun_prop] continuous_map

/-- A `Measure` which is a probability measure can be lifted to a `ProbabilityMeasure`. -/
instance {Y : Type*} [MeasurableSpace Y] :
    CanLift (Measure Y) (ProbabilityMeasure Y) (↑) IsProbabilityMeasure := sorry

/-- A `Measure` which is a finite measure can be lifted to a `FiniteMeasure`. -/
instance {Y : Type*} [MeasurableSpace Y] :
    CanLift (Measure Y) (FiniteMeasure Y) (↑) IsFiniteMeasure := sorry

variable {ι X : Type*} [MeasurableSpace X] [TopologicalSpace X]

variable [DiscreteTopology X] [BorelSpace X]
