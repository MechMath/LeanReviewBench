module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
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

open scoped ENNReal

noncomputable def cubeMeasure {d : ℕ} (Q : TriadicCube d) : MeasureTheory.Measure (Vec d) :=
  MeasureTheory.volume.restrict (cubeSet Q)

noncomputable def normalizedCubeMeasure {d : ℕ} (Q : TriadicCube d) :
    MeasureTheory.Measure (Vec d) :=
  ENNReal.ofReal ((cubeVolume Q)⁻¹) • cubeMeasure Q

instance normalizedCubeMeasure.instIsFiniteMeasure {d : ℕ} (Q : TriadicCube d) :
    MeasureTheory.IsFiniteMeasure (normalizedCubeMeasure Q) := sorry

end Homogenization
