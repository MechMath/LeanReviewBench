module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import dep.Homogenization.Ambient.Basic
public import dep.Homogenization.Geometry.CubeMeasure
public import dep.Homogenization.Geometry.Domain
public import dep.Homogenization.Geometry.TriadicCube
public import dep.Homogenization.Multiscale.CubeAverage

@[expose] public section

namespace Homogenization

open scoped Topology

noncomputable def cubeCenter {d : ℕ} (Q : TriadicCube d) : Vec d :=
  fun i => (Q.index i : ℝ) * cubeScaleFactor Q

noncomputable def cubeRadius {d : ℕ} (Q : TriadicCube d) : ℝ :=
  (1 / 2 : ℝ) * cubeScaleFactor Q

end Homogenization
