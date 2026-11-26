module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.ConjExponents
public import Mathlib.Data.Matrix.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Sum
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import dep.Homogenization.Ambient.Basic
public import dep.Homogenization.Besov.Basic
public import dep.Homogenization.Besov.Duality.Definitions
public import dep.Homogenization.Besov.Duality.Full
public import dep.Homogenization.Besov.Negative
public import dep.Homogenization.Besov.Positive
public import dep.Homogenization.Geometry.CubeMeasure
public import dep.Homogenization.Geometry.CubeMetric
public import dep.Homogenization.Geometry.Domain
public import dep.Homogenization.Geometry.TriadicCube
public import dep.Homogenization.Multiscale.CubeAverage
public import dep.Homogenization.Multiscale.NormalizedNorms

@[expose] public section

namespace Homogenization

open scoped BigOperators ENNReal Topology

theorem CubeBesovDualMeanZeroTestGlobal.memLp {d : ℕ} {Q : TriadicCube d} {s : ℝ}
    {p q : ℝ≥0∞} {g : Vec d → ℝ}
    (hg : CubeBesovDualMeanZeroTestGlobal Q s p q g) :
    MeasureTheory.MemLp g (cubeBesovConjExponent p) (normalizedCubeMeasure Q) := sorry

theorem CubeBesovDualLocalMemLpGlobal.memLp {d : ℕ} {Q : TriadicCube d}
    {p : ℝ≥0∞} {g : Vec d → ℝ}
    (hg : CubeBesovDualLocalMemLpGlobal Q p g) :
    MeasureTheory.MemLp g (cubeBesovConjExponent p) (normalizedCubeMeasure Q) := sorry

theorem CubeBesovDualFullTest.memLp {d : ℕ} {Q : TriadicCube d} {s : ℝ}
    {p q : ℝ≥0∞} {g : Vec d → ℝ} (hg : CubeBesovDualFullTest Q s p q g) :
    MeasureTheory.MemLp g (cubeBesovConjExponent p) (normalizedCubeMeasure Q) := sorry

end Homogenization
