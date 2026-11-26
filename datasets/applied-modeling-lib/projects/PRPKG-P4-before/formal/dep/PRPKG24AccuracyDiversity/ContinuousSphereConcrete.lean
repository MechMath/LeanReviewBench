import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Basic
import Mathlib.LinearAlgebra.AffineSpace.Ordered
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Probability.CDF
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Pareto
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.ProjIcc
import dep.AppliedModelingLib.Applications.RecommenderSystems.Allocation
import dep.AppliedModelingLib.Foundations.Math.Asymptotics
import dep.AppliedModelingLib.Foundations.Probability.OrderStatistics
import dep.AppliedModelingLib.Foundations.Probability.PMFKernel
import dep.PRPKG24AccuracyDiversity.Basic
import dep.PRPKG24AccuracyDiversity.Bernoulli
import dep.PRPKG24AccuracyDiversity.Exchange
import dep.PRPKG24AccuracyDiversity.Representation
import dep.PRPKG24AccuracyDiversity.SeparableAsymptotic
import dep.PRPKG24AccuracyDiversity.TopKOracle
import dep.PRPKG24AccuracyDiversity.Uniform

namespace PRPKG24AccuracyDiversity

open Filter MeasureTheory

open scoped Pointwise

namespace Proposition4Sphere

/-- The paper's unit sphere, as a subtype of the ambient real inner-product space. -/
abbrev UnitSphere (E : Type*) [NormedAddCommGroup E] :=
  {x : E // x ∈ Metric.sphere (0 : E) 1}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Haar-induced surface measure on the unit sphere from an ambient Haar measure. -/
noncomputable abbrev sphereSurfaceMeasure
    [MeasurableSpace E] (μ : MeasureTheory.Measure E) :
    MeasureTheory.Measure (UnitSphere E) :=
  μ.toSphere

/-- Probability-normalized Haar surface measure on the unit sphere. -/
noncomputable abbrev sphereUniformMeasure
    [MeasurableSpace E] (μ : MeasureTheory.Measure E) :
    MeasureTheory.Measure (UnitSphere E) :=
  ((sphereSurfaceMeasure μ) Set.univ)⁻¹ • sphereSurfaceMeasure μ

theorem sphereUniformMeasure_isProbabilityMeasure
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Nontrivial E] (μ : MeasureTheory.Measure E)
    [μ.IsAddHaarMeasure] :
    MeasureTheory.IsProbabilityMeasure (sphereUniformMeasure μ) := sorry

/-- The paper's log radial-distance non-satisfaction kernel. -/
noncomputable def logRadialDistanceKernel
    (p : ℝ → ℝ) (x u : UnitSphere E) : ℝ :=
  Real.log (p (dist (x : E) (u : E)))

/-- The normalized volume surface measure as a probability measure on the sphere. -/
noncomputable def sphereVolumeUniformProbabilityMeasure
    [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E] :
    MeasureTheory.ProbabilityMeasure (UnitSphere E) :=
  ⟨sphereUniformMeasure (MeasureTheory.volume : MeasureTheory.Measure E),
    sphereUniformMeasure_isProbabilityMeasure
      (MeasureTheory.volume : MeasureTheory.Measure E)⟩

/-- User payoff for a probability profile under the log radial-distance kernel. -/
noncomputable def logRadialDistanceProfilePayoff
    [MeasurableSpace E] (p : ℝ → ℝ)
    (alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E))
    (u : UnitSphere E) : ℝ :=
  ∫ x, logRadialDistanceKernel p x u
    ∂(alpha : MeasureTheory.Measure (UnitSphere E))

/-- Supremum objective over users for a probability profile. -/
noncomputable def logRadialDistanceProfileSupValue
    [MeasurableSpace E] (p : ℝ → ℝ)
    (alpha : MeasureTheory.ProbabilityMeasure (UnitSphere E)) : ℝ :=
  sSup (Set.range (logRadialDistanceProfilePayoff (E := E) p alpha))

end Proposition4Sphere

end PRPKG24AccuracyDiversity
