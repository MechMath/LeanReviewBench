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
public import dep.Homogenization.Geometry.ConvexDomain
public import dep.Homogenization.Geometry.CubeMeasure
public import dep.Homogenization.Geometry.CubeMetric
public import dep.Homogenization.Geometry.Domain
public import dep.Homogenization.Geometry.TriadicCube
public import dep.Homogenization.Multiscale.CubeAverage
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

namespace Homogenization

namespace Book

namespace Ch02

noncomputable section

/-- Public Chapter 2 domains: nonempty bounded open convex subsets of `R^d`. -/
structure Domain (d : ℕ) where
  carrier : Set (Vec d)
  isDomain : IsOpenBoundedConvexDomain carrier
  nonempty : carrier.Nonempty

namespace Domain

instance {d : ℕ} : Coe (Domain d) (Set (Vec d)) where
  coe U := U.carrier

theorem isBoundedDomain {d : ℕ} (U : Domain d) :
    IsBoundedDomain (U : Set (Vec d)) := sorry

theorem measurableSet {d : ℕ} (U : Domain d) : MeasurableSet (U : Set (Vec d)) := sorry

instance instIsFiniteMeasureVolumeMeasureOn {d : ℕ} (U : Domain d) :
    MeasureTheory.IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d))) := sorry

end Domain

/-- Public version of `a in Omega(U)`.

This is deliberately an almost-everywhere object: the coefficient field is a
representative, and all public regularity/ellipticity data is stated with respect
to `volumeMeasureOn U`.
-/
structure CoeffOn {d : ℕ} (U : Domain d) where
  toCoeffField : CoeffField d
  lam : ℝ
  Lam : ℝ
  lam_pos : 0 < lam
  lam_le_Lam : lam ≤ Lam
  aeStronglyMeasurable :
    ∀ i j : Fin d,
      MeasureTheory.AEStronglyMeasurable
        (fun x : Vec d => restrictCoeffField (U : Set (Vec d)) toCoeffField x i j)
        (volumeMeasureOn (U : Set (Vec d)))
  aeElliptic :
    ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
      IsEllipticMatrix lam Lam (toCoeffField x)

namespace CoeffOn

instance {d : ℕ} {U : Domain d} : CoeFun (CoeffOn U) (fun _ => CoeffField d) where
  coe a := a.toCoeffField

theorem measurableSet {d : ℕ} {U : Domain d} (_a : CoeffOn U) :
    MeasurableSet (U : Set (Vec d)) := sorry

/-- Public adjoint coefficient field `a^t`, still as an a.e. coefficient object
on the same Chapter 2 domain. -/
noncomputable def transpose {d : ℕ} {U : Domain d} (a : CoeffOn U) : CoeffOn U where
  toCoeffField := fun x => matTranspose (a.toCoeffField x)
  lam := a.lam
  Lam := a.Lam
  lam_pos := a.lam_pos
  lam_le_Lam := a.lam_le_Lam
  aeStronglyMeasurable := sorry
  aeElliptic := sorry

/-- Equality of public coefficient fields is equality of representatives almost
everywhere on the public domain. -/
def AEEq {d : ℕ} {U : Domain d} (a b : CoeffOn U) : Prop :=
  a.toCoeffField =ᵐ[volumeMeasureOn (U : Set (Vec d))] b.toCoeffField

/-- `b` is the restriction of `a` to a smaller public domain, modulo null sets.

This is deliberately an a.e. relation between coefficient representatives, rather
than a pointwise restriction definition. -/
def RestrictsTo {d : ℕ} {U V : Domain d} (a : CoeffOn U) (b : CoeffOn V) : Prop :=
  b.toCoeffField =ᵐ[volumeMeasureOn (V : Set (Vec d))] a.toCoeffField

namespace AEEq

end AEEq

theorem AEEq.transpose {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : AEEq a b) : AEEq a.transpose b.transpose := sorry

end CoeffOn

/-- Public Chapter 2 notation for `A(U; a)`. -/
abbrev Solution {d : ℕ} (U : Domain d) (a : CoeffOn U) :=
  AHarmonicFunction a.toCoeffField (U : Set (Vec d))

namespace Solution

/-- Two public solutions have the same gradient on `U`, modulo null sets. -/
def SameGradientAE {d : ℕ} {U : Domain d} {a : CoeffOn U}
    (u v : Solution U a) : Prop :=
  u.toH1.grad =ᵐ[volumeMeasureOn (U : Set (Vec d))] v.toH1.grad

namespace SameGradientAE

end SameGradientAE

end Solution

end

end Ch02

end Book

end Homogenization
