module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Sum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Bounded
public import dep.Homogenization.Ambient.Basic
public import dep.Homogenization.Geometry.CubeMeasure
public import dep.Homogenization.Geometry.Domain
public import dep.Homogenization.Geometry.TriadicCube
public import dep.Homogenization.Multiscale.CubeAverage
public import dep.Homogenization.Multiscale.NormalizedNorms

@[expose] public section

namespace Homogenization

open scoped BigOperators ENNReal

noncomputable def cubeBesovOscillation {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞)
    (u : Vec d → ℝ) : ℝ :=
  cubeLpNorm Q p (cubeFluctuation Q u)

noncomputable def cubeBesovScaleWeight {d : ℕ} (s : ℝ) (Q : TriadicCube d) : ℝ :=
  (cubeScaleFactor Q) ^ (-s)

noncomputable def descendantsAverage {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (F : TriadicCube d → ℝ) : ℝ := by
  let D := descendantsAtDepth Q j
  exact ((D.card : ℝ)⁻¹) * D.sum F

end Homogenization
