module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Bounded
public import dep.Homogenization.Ambient.Basic
public import dep.Homogenization.Geometry.Domain
public import dep.Homogenization.Geometry.TriadicCube

@[expose] public section

namespace Homogenization

theorem measurableSet_cubeSet {d : ℕ} (Q : TriadicCube d) :
    MeasurableSet (cubeSet Q) := sorry

end Homogenization
