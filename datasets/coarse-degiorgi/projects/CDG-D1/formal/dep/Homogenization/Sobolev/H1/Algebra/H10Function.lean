module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
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
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
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
public import dep.Homogenization.Geometry.Domain
public import dep.Homogenization.Geometry.TriadicCube
public import dep.Homogenization.Multiscale.NormalizedNorms
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

namespace H10Function

instance {d : ℕ} {U : Set (Vec d)} : Zero (H10Function U) where
  zero :=
    { toH1Function := 0
      approx := fun _ => 0
      approx_smooth := sorry
      approx_hasCompactSupport := sorry
      approx_support_subset := sorry
      tendsto_approx := sorry
      tendsto_approx_grad := sorry }

instance {d : ℕ} {U : Set (Vec d)} : SMul ℝ (H10Function U) where
  smul c u :=
    { toH1Function := c • u.toH1Function
      approx := fun n x => c * u.approx n x
      approx_smooth := sorry
      approx_hasCompactSupport := sorry
      approx_support_subset := sorry
      tendsto_approx := sorry
      tendsto_approx_grad := sorry }

instance {d : ℕ} {U : Set (Vec d)} : Neg (H10Function U) where
  neg u := (-1 : ℝ) • u

instance {d : ℕ} {U : Set (Vec d)} : Add (H10Function U) where
  add u v :=
    { toH1Function := u.toH1Function + v.toH1Function
      approx := fun n x => u.approx n x + v.approx n x
      approx_smooth := sorry
      approx_hasCompactSupport := sorry
      approx_support_subset := sorry
      tendsto_approx := sorry
      tendsto_approx_grad := sorry }

instance {d : ℕ} {U : Set (Vec d)} : Sub (H10Function U) where
  sub u v := u + (-v)

end H10Function

end Homogenization
