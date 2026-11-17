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
public import dep.Homogenization.Ambient.Euclidean
public import dep.Homogenization.Ambient.HilbertFinite
public import dep.Homogenization.Geometry.CubeMeasure
public import dep.Homogenization.Geometry.CubeMetric
public import dep.Homogenization.Geometry.Domain
public import dep.Homogenization.Geometry.TriadicCube
public import dep.Homogenization.Multiscale.CubeAverage
public import dep.Homogenization.Sobolev.Foundations.Cutoff.Cube
public import dep.Homogenization.Sobolev.Foundations.Cutoff.Euclidean
public import dep.Homogenization.Sobolev.Foundations.Cutoff.Profile
public import dep.Homogenization.Sobolev.WeakDerivatives

@[expose] public section

noncomputable section

open Set

open scoped Topology

namespace Homogenization

/-- Dimensional first-derivative constant for the ball cutoff interface.

The factor `d` accounts for measuring derivatives on `Vec d` using the default
sup/product norm. -/
def quantitativeBallCutoffGradientConst (d : ℕ) : ℝ :=
  8 * (d : ℝ) * smoothTransitionProfile.derivBound

/-- Dimensional Hessian constant for the ball cutoff interface. -/
def quantitativeBallCutoffHessianConst (d : ℕ) : ℝ :=
  32 * (d : ℝ) ^ 2 *
    max 1 (max smoothTransitionProfile.derivBound smoothTransitionProfile.secondDerivBound)

/-- Dimensional first-derivative constant for the cube cutoff interface. -/
def quantitativeCubeCutoffGradientConst (d : ℕ) : ℝ :=
  8 * (d : ℝ) * smoothTransitionProfile.derivBound

/-- Dimensional Hessian constant for the cube cutoff interface. -/
def quantitativeCubeCutoffHessianConst (d : ℕ) : ℝ :=
  8 * (d : ℝ) ^ 2 *
    (max 1
      (max smoothTransitionProfile.derivBound smoothTransitionProfile.secondDerivBound)) ^ 2

/-- A quantitative smooth cutoff between two concentric balls. -/
structure QuantitativeBallCutoff {d : ℕ} (x₀ : Vec d) (r R : ℝ) where
  toFun : Vec d → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  hasCompactSupport : HasCompactSupport toFun
  support_subset : tsupport toFun ⊆ euclideanBall x₀ R
  nonneg : ∀ x, 0 ≤ toFun x
  le_one : ∀ x, toFun x ≤ 1
  eq_one_on_inner : ∀ x ∈ euclideanBall x₀ r, toFun x = 1
  gradient_bound : ∀ x, ‖fderiv ℝ toFun x‖ ≤
    quantitativeBallCutoffGradientConst d / (R - r)
  hessian_bound :
    ∀ x, ‖iteratedFDeriv ℝ 2 toFun x‖ ≤
      quantitativeBallCutoffHessianConst d / (R - r) ^ 2

namespace QuantitativeBallCutoff

instance {d : ℕ} {x₀ : Vec d} {r R : ℝ} :
    CoeFun (QuantitativeBallCutoff x₀ r R) (fun _ => Vec d → ℝ) where
  coe η := η.toFun

end QuantitativeBallCutoff

/-- A quantitative smooth cutoff between two concentric subcubes of a triadic cube. -/
structure QuantitativeCubeCutoff {d : ℕ} (Q : TriadicCube d) (ρ₁ ρ₂ : ℝ) where
  toFun : Vec d → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  hasCompactSupport : HasCompactSupport toFun
  support_subset : Function.support toFun ⊆ scaledOpenCubeSet Q ρ₂
  nonneg : ∀ x, 0 ≤ toFun x
  le_one : ∀ x, toFun x ≤ 1
  eq_one_on_inner : ∀ x ∈ scaledClosedCubeSet Q ρ₁, toFun x = 1
  gradient_bound : ∀ x,
    ‖fderiv ℝ toFun x‖ ≤
      quantitativeCubeCutoffGradientConst d / ((ρ₂ - ρ₁) * cubeRadius Q)
  hessian_bound : ∀ x,
    ‖iteratedFDeriv ℝ 2 toFun x‖ ≤
      quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2)

namespace QuantitativeCubeCutoff

instance {d : ℕ} {Q : TriadicCube d} {ρ₁ ρ₂ : ℝ} :
    CoeFun (QuantitativeCubeCutoff Q ρ₁ ρ₂) (fun _ => Vec d → ℝ) where
  coe η := η.toFun

end QuantitativeCubeCutoff

end Homogenization
