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
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.Normed.Module.Convex
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
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Order.Compact
public import dep.Homogenization.Ambient.Basic
public import dep.Homogenization.Ambient.BlockMatrix
public import dep.Homogenization.Ambient.HilbertFinite
public import dep.Homogenization.Geometry.ConvexDomain
public import dep.Homogenization.Geometry.CubeMeasure
public import dep.Homogenization.Geometry.Domain
public import dep.Homogenization.Geometry.TriadicCube
public import dep.Homogenization.Multiscale.CubeAverage
public import dep.Homogenization.Multiscale.NormalizedNorms
public import dep.Homogenization.Sobolev.Foundations.CoerciveH1
public import dep.Homogenization.Sobolev.Foundations.H1Graph.Graph
public import dep.Homogenization.Sobolev.Foundations.H1Graph.Preliminaries
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

section CoerciveHilbert

variable {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]

/-- The canonical complete Hilbert carrier for the mean-zero coercive `H¹`
layer: the closed mean-zero weak-gradient graph inside
`L²(U) × L²(U; HilbertVec d)`. -/
noncomputable abbrev H1CoerciveHilbertAmbient :=
  WithLp 2 (ScalarL2 U × HilbertVectorL2 U)

noncomputable abbrev h1CoerciveHilbertAmbientEquiv :
    H1CoerciveHilbertAmbient (U := U) ≃L[ℝ] ScalarL2 U × HilbertVectorL2 U :=
  WithLp.prodContinuousLinearEquiv 2 ℝ (ScalarL2 U) (HilbertVectorL2 U)

noncomputable abbrev h1CoerciveHilbertClosedSubmodule :
    ClosedSubmodule ℝ (H1CoerciveHilbertAmbient (U := U)) :=
  (h1MeanZeroGraphClosedSubmodule (U := U)).comap
    (h1CoerciveHilbertAmbientEquiv (U := U)).toContinuousLinearMap

noncomputable abbrev h1CoerciveHilbertSubmodule :
    Submodule ℝ (H1CoerciveHilbertAmbient (U := U)) :=
  (h1CoerciveHilbertClosedSubmodule (U := U)).toSubmodule

noncomputable abbrev H1CoerciveHilbertSpace :=
  ↥(h1CoerciveHilbertSubmodule (U := U))

namespace H1CoerciveHilbert

noncomputable instance : SeminormedAddCommGroup (H1CoerciveHilbertSpace (U := U)) := by
  exact inferInstanceAs (SeminormedAddCommGroup (h1CoerciveHilbertSubmodule (U := U)))

noncomputable instance : NormedAddCommGroup (H1CoerciveHilbertSpace (U := U)) := by
  exact inferInstanceAs (NormedAddCommGroup (h1CoerciveHilbertSubmodule (U := U)))

noncomputable instance : NormedSpace ℝ (H1CoerciveHilbertSpace (U := U)) := by
  exact inferInstanceAs (NormedSpace ℝ (h1CoerciveHilbertSubmodule (U := U)))

noncomputable instance : InnerProductSpace ℝ (H1CoerciveHilbertSpace (U := U)) := by
  exact inferInstanceAs (InnerProductSpace ℝ (h1CoerciveHilbertSubmodule (U := U)))

noncomputable instance : CompleteSpace (H1CoerciveHilbertSpace (U := U)) := sorry

/-- The scalar `L²(U)` value component of a point in the coercive Hilbert
graph. -/
abbrev value (z : H1CoerciveHilbertSpace (U := U)) : ScalarL2 U :=
  z.1.fst

end H1CoerciveHilbert

namespace H1MeanZeroFunction

end H1MeanZeroFunction

namespace H1Function

end H1Function

end CoerciveHilbert

end Homogenization
