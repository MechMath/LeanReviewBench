module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Set.Function
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Order.Compact
public import dep.Homogenization.Ambient.Basic
public import dep.Homogenization.Geometry.ConvexDomain
public import dep.Homogenization.Geometry.CubeMeasure
public import dep.Homogenization.Geometry.Domain
public import dep.Homogenization.Geometry.TriadicCube

@[expose] public section

namespace Homogenization

open MeasureTheory Metric

open scoped ENNReal NNReal Pointwise

section NeZero

variable {d : ℕ} [NeZero d]

/-- Cache `Nontrivial (Vec d)` once per section so tactic-level typeclass
searches don't rediscover the NeZero → Nonempty → Nontrivial chain. -/
private instance instNontrivialVecNeZero : Nontrivial (Vec d) := sorry

end NeZero

section BoundedDomain

variable {d : ℕ} {U : Set (Vec d)} [NeZero d]

/-- Cache `Nontrivial (Vec d)` once per section. -/
private instance instNontrivialVecBounded : Nontrivial (Vec d) := sorry

end BoundedDomain

end Homogenization
