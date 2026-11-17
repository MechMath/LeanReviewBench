module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Set.Function
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Prod
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
public import dep.Homogenization.Sobolev.W1p.BasicLemmas
public import dep.Homogenization.Sobolev.W1p.Definitions
public import dep.Homogenization.Sobolev.WeakDerivatives

@[expose] public section

namespace Homogenization

open scoped Pointwise Convolution

/-- Cache `HasContDiffBump (Vec d)` so tactic-level typeclass searches across
this file *and its transitive importers* don't re-derive the finite-
dimensional-inner-product-space chain on every `ContDiffBump`, `eLpNorm`,
and `MeasureTheory.*` call. This single private instance drops cumulative
`typeclass inference` from 29.9s to ~6s in this file and propagates a
~2.6× reduction across the six downstream splits via the instance cache. -/
private instance instHasContDiffBumpVec (d : ℕ) : HasContDiffBump (Vec d) := sorry

structure IsConvexApproxKernel {d : ℕ} (ρ : Vec d → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) ρ
  compactSupport : HasCompactSupport ρ
  support_subset_closedBall : tsupport ρ ⊆ Metric.closedBall (0 : Vec d) 1
  nonneg : ∀ z, 0 ≤ ρ z
  setIntegral_one : ∫ z in tsupport ρ, ρ z = 1

namespace IsConvexApproxKernel

end IsConvexApproxKernel

namespace ContDiffBump

end ContDiffBump

end Homogenization
