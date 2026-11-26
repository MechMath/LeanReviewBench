module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Pointwise
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import dep.Homogenization.Ambient.Basic
public import dep.Homogenization.Ambient.BlockMatrix
public import dep.Homogenization.Ambient.Euclidean
public import dep.Homogenization.Ambient.HilbertFinite
public import dep.Homogenization.Geometry.CubeMeasure
public import dep.Homogenization.Geometry.CubeMetric
public import dep.Homogenization.Geometry.Domain
public import dep.Homogenization.Geometry.TriadicCube
public import dep.Homogenization.Multiscale.CubeAverage
public import dep.Homogenization.Sobolev.Foundations.Cutoff.Euclidean
public import dep.Homogenization.Sobolev.Foundations.Cutoff.Profile
public import dep.Homogenization.Sobolev.WeakDerivatives

@[expose] public section

noncomputable section

open scoped BigOperators Topology

open Set

namespace Homogenization

/-- Closed concentric subcube of relative radius `ρ` inside a triadic cube. -/
def scaledClosedCubeSet {d : ℕ} (Q : TriadicCube d) (ρ : ℝ) : Set (Vec d) :=
  {x | ∀ i, |x i - cubeCenter Q i| ≤ ρ * cubeRadius Q}

/-- Open concentric subcube of relative radius `ρ` inside a triadic cube. -/
def scaledOpenCubeSet {d : ℕ} (Q : TriadicCube d) (ρ : ℝ) : Set (Vec d) :=
  {x | ∀ i, |x i - cubeCenter Q i| < ρ * cubeRadius Q}

namespace QuantitativeTransitionProfile

end QuantitativeTransitionProfile

end Homogenization
