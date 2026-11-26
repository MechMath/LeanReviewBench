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
public import dep.Homogenization.Ambient.HilbertFinite
public import dep.Homogenization.Geometry.ConvexDomain
public import dep.Homogenization.Geometry.CubeMeasure
public import dep.Homogenization.Geometry.Domain
public import dep.Homogenization.Geometry.TriadicCube
public import dep.Homogenization.Multiscale.CubeAverage
public import dep.Homogenization.Multiscale.NormalizedNorms
public import dep.Homogenization.Sobolev.Foundations.CoerciveH1
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

section Graph

variable {d : ℕ} {U : Set (Vec d)}

/-- The weak-gradient constraint attached to a coordinate `i` and a smooth
compactly supported test function `φ`. Its kernel consists of pairs
`(u, Du) ∈ L²(U) × L²(U; HilbertVec d)` satisfying the corresponding
integration-by-parts identity. -/
noncomputable def h1WeakConstraintCLM (i : Fin d) (φ : H1WeakTestFunction U) :
    (ScalarL2 U × HilbertVectorL2 U) →L[ℝ] ℝ :=
  ((InnerProductSpace.toDual ℝ (ScalarL2 U) (φ.derivToScalarL2 i)).comp
      (ContinuousLinearMap.fst ℝ (ScalarL2 U) (HilbertVectorL2 U))) +
    (((InnerProductSpace.toDual ℝ (ScalarL2 U) φ.toScalarL2).comp
        (hilbertVectorCoordToScalarL2 (U := U) i)).comp
      (ContinuousLinearMap.snd ℝ (ScalarL2 U) (HilbertVectorL2 U)))

/-- The closed ambient subspace cut out by the weak-gradient constraints. -/
noncomputable def h1GraphClosedSubmodule :
    ClosedSubmodule ℝ (ScalarL2 U × HilbertVectorL2 U) :=
  ⨅ i : Fin d, ⨅ φ : H1WeakTestFunction U,
    (⊥ : ClosedSubmodule ℝ ℝ).comap (h1WeakConstraintCLM (U := U) i φ)

end Graph

section MeanZero

variable {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]

/-- The constant-one class in scalar `L²(U)`. -/
noncomputable def oneScalarL2 : ScalarL2 U :=
  Homogenization.toScalarL2
    (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (p := (2 : ENNReal)) (c := (1 : ℝ)))

/-- The scalar integral on `L²(U)` for finite-measure domains. -/
noncomputable def scalarIntegralCLM : ScalarL2 U →L[ℝ] ℝ :=
  InnerProductSpace.toDual ℝ (ScalarL2 U) (oneScalarL2 (U := U))

namespace H1Function

end H1Function

/-- The closed mean-zero weak-gradient graph in
`L²(U) × L²(U; HilbertVec d)`. -/
noncomputable def h1MeanZeroGraphClosedSubmodule :
    ClosedSubmodule ℝ (ScalarL2 U × HilbertVectorL2 U) :=
  h1GraphClosedSubmodule (U := U) ⊓
    (⊥ : ClosedSubmodule ℝ ℝ).comap
      ((scalarIntegralCLM (U := U)).comp
        (ContinuousLinearMap.fst ℝ (ScalarL2 U) (HilbertVectorL2 U)))

end MeanZero

end Homogenization
