module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import dep.Homogenization.Ambient.Basic
public import dep.Homogenization.Geometry.BoundedMeasurableDomain
public import dep.Homogenization.Geometry.CubeMeasure
public import dep.Homogenization.Geometry.CubeMetric
public import dep.Homogenization.Geometry.Domain
public import dep.Homogenization.Geometry.TriadicCube
public import dep.Homogenization.Multiscale.CubeAverage
public import dep.Homogenization.Multiscale.NormalizedNorms

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

/-- The half-open carrier of a triadic cube, packaged with its geometric
regularity and positive volume. -/
noncomputable def cubeBoundedMeasurableDomain {d : ℕ} (Q : TriadicCube d) :
    BoundedMeasurableDomain d where
  carrier := cubeSet Q
  measurableSet := measurableSet_cubeSet Q
  isBoundedDomain := sorry
  volume_pos := sorry

end

end Homogenization
