module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.ConjExponents
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
public import dep.Homogenization.Besov.Basic
public import dep.Homogenization.Besov.Duality.Definitions
public import dep.Homogenization.Besov.Negative
public import dep.Homogenization.Besov.Positive
public import dep.Homogenization.Geometry.CubeMeasure
public import dep.Homogenization.Geometry.Domain
public import dep.Homogenization.Geometry.TriadicCube
public import dep.Homogenization.Multiscale.CubeAverage
public import dep.Homogenization.Multiscale.NormalizedNorms

@[expose] public section

namespace Homogenization

open MeasureTheory.Measure

open scoped BigOperators ENNReal

noncomputable def CubeBesovDualLocalMemLpGlobal {d : ℕ} (Q : TriadicCube d)
    (p : ℝ≥0∞) (g : Vec d → ℝ) : Prop :=
  ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
    MeasureTheory.MemLp (cubeFluctuation R g) (cubeBesovConjExponent p)
      (normalizedCubeMeasure R)

def CubeBesovDualFullTest {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (g : Vec d → ℝ) : Prop :=
  (∀ N : ℕ, cubeBesovDualTestNorm Q s p q N g ≤ 1) ∧
    CubeBesovDualLocalMemLpGlobal Q p g

def CubeBesovDualMeanZeroTestGlobal {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (g : Vec d → ℝ) : Prop :=
  (∀ N : ℕ, cubeBesovDualTestSeminorm Q s p q N g ≤ 1) ∧
    cubeAverage Q g = 0 ∧ CubeBesovDualLocalMemLpGlobal Q p g

end Homogenization
