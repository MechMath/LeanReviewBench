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
public import Mathlib.MeasureTheory.Integral.Prod
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
public import dep.Homogenization.Geometry.Domain
public import dep.Homogenization.Geometry.TriadicCube
public import dep.Homogenization.Sobolev.Foundations.PoincareLpKernel.Basic

@[expose] public section

namespace Homogenization

open MeasureTheory Metric

open scoped ENNReal NNReal Pointwise

section SegmentChangeOfVariables

set_option linter.unusedSectionVars false

variable {d : ℕ} [NeZero d]

/-- File-level typeclass cache for `Nontrivial (Vec d)` under `[NeZero d]`.
Repeated inference of this head class dominates the file (~7s cumulative
typeclass before the cache). The cache fires during elaboration of theorems
in this section even when their type signatures don't use `[NeZero d]`,
because the variable-block instance is in scope for typeclass search. -/
private instance instNontrivialVecSegCV (d : ℕ) [NeZero d] :
    Nontrivial (Vec d) := sorry

end SegmentChangeOfVariables

end Homogenization
