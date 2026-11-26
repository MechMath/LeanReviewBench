module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Function
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Order.Compact
public import dep.Homogenization.Ambient.Basic
public import dep.Homogenization.Ambient.HilbertFinite
public import dep.Homogenization.Geometry.ConvexDomain
public import dep.Homogenization.Geometry.CubeMeasure
public import dep.Homogenization.Geometry.Domain
public import dep.Homogenization.Geometry.TriadicCube
public import dep.Homogenization.Multiscale.CubeAverage
public import dep.Homogenization.Multiscale.NormalizedNorms
public import dep.Homogenization.Sobolev.Foundations.PoincareLpKernel.Basic
public import dep.Homogenization.Sobolev.Foundations.PoincareLpKernel.RieszPowerMean
public import dep.Homogenization.Sobolev.Foundations.PoincareLpKernel.SegmentChangeOfVariables
public import dep.Homogenization.Sobolev.Foundations.PoincareLpKernel.TimeCollapse
public import dep.Homogenization.Sobolev.Foundations.PoincareW1p.Seminorms
public import dep.Homogenization.Sobolev.H1.Algebra.H10Function
public import dep.Homogenization.Sobolev.H1.Algebra.H1Function
public import dep.Homogenization.Sobolev.H1.BasicLemmas
public import dep.Homogenization.Sobolev.H1.Definitions
public import dep.Homogenization.Sobolev.L2Ambient
public import dep.Homogenization.Sobolev.W1p.BasicLemmas
public import dep.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Kernel
public import dep.Homogenization.Sobolev.W1p.Definitions
public import dep.Homogenization.Sobolev.WeakDerivatives

@[expose] public section

namespace Homogenization

open scoped ENNReal

namespace W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ENNReal}

end W1pFunction

/-- Mean-zero `W^{1,p}(U)` functions, represented by a chosen witness together
with the zero-average condition. -/
structure W1pMeanZeroFunction {d : ℕ} (U : Set (Vec d)) (p : ENNReal) where
  toW1pFunction : W1pFunction U p
  meanZero : MeanZeroOn U toW1pFunction.toFun

namespace W1pMeanZeroFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ENNReal}

instance : Coe (W1pMeanZeroFunction U p) (W1pFunction U p) where
  coe u := u.toW1pFunction

instance : CoeFun (W1pMeanZeroFunction U p) (fun _ => Vec d → ℝ) where
  coe u := u.toW1pFunction.toFun

/-- The scalar `L^p(U)` seminorm of a mean-zero `W^{1,p}` function. -/
noncomputable def valueLpSeminorm (u : W1pMeanZeroFunction U p) : ℝ :=
  u.toW1pFunction.valueLpSeminorm

/-- Coordinate-sum gradient seminorm of a mean-zero `W^{1,p}` function. -/
noncomputable def gradientCoordLpSeminormSum (u : W1pMeanZeroFunction U p) : ℝ :=
  u.toW1pFunction.gradientCoordLpSeminormSum

end W1pMeanZeroFunction

/-- A bundled finite-`p` mean-zero Poincare estimate for the `W^{1,p}` layer. -/
structure W1pPoincareEstimate {d : ℕ} (U : Set (Vec d)) (p : ENNReal) where
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  bound :
    ∀ u : W1pMeanZeroFunction U p,
      u.valueLpSeminorm ≤ constant * u.gradientCoordLpSeminormSum

namespace W1pPoincareEstimate

variable {d : ℕ} {U : Set (Vec d)} {p : ENNReal}

end W1pPoincareEstimate

end Homogenization
