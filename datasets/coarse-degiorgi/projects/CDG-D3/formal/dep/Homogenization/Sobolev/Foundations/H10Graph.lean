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
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
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
public import Mathlib.LinearAlgebra.Pi
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
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
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
public import dep.Homogenization.Sobolev.Foundations.CoerciveH1
public import dep.Homogenization.Sobolev.Foundations.H1Graph.CoerciveHilbert
public import dep.Homogenization.Sobolev.Foundations.H1Graph.Graph
public import dep.Homogenization.Sobolev.Foundations.H1Graph.Preliminaries
public import dep.Homogenization.Sobolev.Foundations.PoincareLpKernel.Basic
public import dep.Homogenization.Sobolev.Foundations.PoincareLpKernel.RieszPowerMean
public import dep.Homogenization.Sobolev.Foundations.PoincareLpKernel.SegmentChangeOfVariables
public import dep.Homogenization.Sobolev.Foundations.PoincareLpKernel.TimeCollapse
public import dep.Homogenization.Sobolev.Foundations.PoincareW1p.Core
public import dep.Homogenization.Sobolev.Foundations.PoincareW1p.Seminorms
public import dep.Homogenization.Sobolev.Foundations.PoincareZeroTrace
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

open scoped RealInnerProductSpace

variable {d : ℕ} {U : Set (Vec d)}

/-- The graph of the typed `H¹₀(U)` realization inside
`L²(U) × L²(U; ℝᵈ)`. -/
noncomputable def h10GraphSubmodule
    (U : Set (Vec d)) : Submodule ℝ (ScalarL2 U × HilbertVectorL2 U) where
  carrier :=
    {z | ∃ u : H10Function U,
      u.toH1Function.toScalarL2 = z.1 ∧
      u.toH1Function.gradToHilbertVectorL2 = z.2}
  zero_mem' := sorry
  add_mem' := sorry
  smul_mem' := sorry

/-- The closed `H¹₀` graph in the typed Hilbert product. -/
noncomputable def h10GraphClosedSubmodule
    (U : Set (Vec d)) : ClosedSubmodule ℝ (ScalarL2 U × HilbertVectorL2 U) :=
  (h10GraphSubmodule U).closure

/-- The closed `H¹₀` graph as a normed carrier. -/
noncomputable abbrev H10GraphClosedSpace (U : Set (Vec d)) :=
  ↥((h10GraphClosedSubmodule U).toSubmodule)

namespace H10GraphClosed

noncomputable instance : CompleteSpace (H10GraphClosedSpace (d := d) U) := sorry

/-- Scalar value component of a closed `H¹₀` graph point. -/
abbrev value (z : H10GraphClosedSpace (d := d) U) : ScalarL2 U :=
  z.1.1

end H10GraphClosed

end Homogenization
