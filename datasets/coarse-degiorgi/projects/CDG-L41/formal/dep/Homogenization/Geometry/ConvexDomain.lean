module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Order.Compact
public import dep.Homogenization.Ambient.Basic
public import dep.Homogenization.Geometry.CubeMeasure
public import dep.Homogenization.Geometry.Domain
public import dep.Homogenization.Geometry.TriadicCube

@[expose] public section

namespace Homogenization

theorem Bornology.IsBounded.isBoundedDomain {d : ℕ} {U : Set (Vec d)}
    (hU : Bornology.IsBounded U) : IsBoundedDomain U := sorry

/-- Bounded open convex domains in the ambient space `Vec d = Fin d → ℝ`. -/
def IsOpenBoundedConvexDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  IsOpen U ∧ IsBoundedDomain U ∧ Convex ℝ U

namespace IsOpenBoundedConvexDomain

theorem isBoundedDomain {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) :
    IsBoundedDomain U := sorry

end IsOpenBoundedConvexDomain

namespace IsSobolevRegularDomain

end IsSobolevRegularDomain

theorem isOpenBoundedConvexDomain_openCubeSet {d : ℕ} (Q : TriadicCube d) :
    IsOpenBoundedConvexDomain (openCubeSet Q) := sorry

end Homogenization
