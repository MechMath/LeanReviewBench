module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.CStarAlgebra.Matrix
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
public import Mathlib.MeasureTheory.Integral.Average
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
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.Order.Compact
public import dep.Homogenization.Ambient.Basic
public import dep.Homogenization.Ambient.CoefficientField
public import dep.Homogenization.Ambient.HilbertFinite
public import dep.Homogenization.Book.Ch02.Matrices
public import dep.Homogenization.Book.Ch02.Response
public import dep.Homogenization.Book.Ch02.Setup
public import dep.Homogenization.Geometry.ConvexDomain
public import dep.Homogenization.Geometry.Domain
public import dep.Homogenization.Geometry.TriadicCube
public import dep.Homogenization.Multiscale.NormalizedNorms
public import dep.Homogenization.PDE.Harmonic
public import dep.Homogenization.Sobolev.Foundations.CoerciveH1
public import dep.Homogenization.Sobolev.Foundations.H1Graph.CoerciveHilbert
public import dep.Homogenization.Sobolev.Foundations.H1Graph.Graph
public import dep.Homogenization.Sobolev.Foundations.H1Graph.Preliminaries
public import dep.Homogenization.Sobolev.Foundations.PoincareLpKernel.Basic
public import dep.Homogenization.Sobolev.Foundations.PoincareLpKernel.RieszPowerMean
public import dep.Homogenization.Sobolev.Foundations.PoincareLpKernel.SegmentChangeOfVariables
public import dep.Homogenization.Sobolev.Foundations.PoincareLpKernel.TimeCollapse
public import dep.Homogenization.Sobolev.Foundations.PoincareMeanZero
public import dep.Homogenization.Sobolev.H1.Algebra.H10Function
public import dep.Homogenization.Sobolev.H1.Algebra.H1Function
public import dep.Homogenization.Sobolev.H1.BasicLemmas
public import dep.Homogenization.Sobolev.H1.Definitions
public import dep.Homogenization.Sobolev.L2Ambient
public import dep.Homogenization.Sobolev.PotentialSolenoidal
public import dep.Homogenization.Sobolev.W1p.BasicLemmas
public import dep.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Kernel
public import dep.Homogenization.Sobolev.W1p.Definitions
public import dep.Homogenization.Sobolev.WeakDerivatives

@[expose] public section

open scoped BigOperators

namespace Homogenization

namespace Book

namespace Ch02

noncomputable section

/-- The open realization of a triadic cube is a nonempty public Chapter 2
domain. -/
theorem openCubeSet_nonempty {d : ℕ} (Q : TriadicCube d) :
    (openCubeSet Q).Nonempty := sorry

/-- The public Chapter 2 domain associated with an open triadic cube. -/
noncomputable def cubeDomain {d : ℕ} (Q : TriadicCube d) : Domain d where
  carrier := openCubeSet Q
  isDomain := isOpenBoundedConvexDomain_openCubeSet Q
  nonempty := openCubeSet_nonempty Q

/-- A coefficient field on the triadic cube hierarchy.

For each open triadic cube it provides a `CoeffOn` object, hence ellipticity and
measurability are a.e. on that cube.  The `restrictsTo_of_subset` field says
that the representatives are compatible across nested cubes only modulo null
sets; this is the public replacement for old representative-level cube
restrictions. -/
structure TriadicCoeffFamily (d : ℕ) where
  coeffOn : (Q : TriadicCube d) → CoeffOn (cubeDomain Q)
  restrictsTo_of_subset :
    ∀ {Q R : TriadicCube d}, openCubeSet R ⊆ openCubeSet Q →
      CoeffOn.RestrictsTo (coeffOn Q) (coeffOn R)

namespace TriadicCoeffFamily

/-- Two triadic coefficient families are equal when their cube representatives
agree a.e. on every open triadic cube. -/
def AEEq {d : ℕ} (a b : TriadicCoeffFamily d) : Prop :=
  ∀ Q : TriadicCube d, CoeffOn.AEEq (a.coeffOn Q) (b.coeffOn Q)

namespace AEEq

end AEEq

end TriadicCoeffFamily

/-- Exponents used in the multiscale ellipticity constants: finite `q` and the
endpoint `q = infinity`. -/
inductive MultiscaleExponent where
  | finite (value : ℝ)
  | infinity
deriving DecidableEq

namespace MultiscaleExponent

end MultiscaleExponent

end

end Ch02

end Book

end Homogenization
