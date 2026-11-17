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
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
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
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Basic
import Mathlib.LinearAlgebra.AffineSpace.Ordered
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.Floor
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
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Probability.CDF
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Pareto
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import dep.AppliedModelingLib.Applications.RecommenderSystems.Allocation
import dep.AppliedModelingLib.Foundations.Math.Asymptotics
import dep.AppliedModelingLib.Foundations.Probability.OrderStatistics
import dep.AppliedModelingLib.Foundations.Probability.PMFKernel
import dep.PRPKG24AccuracyDiversity.AppendixD1GenericIIFull
import dep.PRPKG24AccuracyDiversity.AppendixD1GenericIII
import dep.PRPKG24AccuracyDiversity.AppendixD1GenericIV
import dep.PRPKG24AccuracyDiversity.AppendixD1GenericPower
import dep.PRPKG24AccuracyDiversity.Assumptions
import dep.PRPKG24AccuracyDiversity.Basic
import dep.PRPKG24AccuracyDiversity.Bernoulli
import dep.PRPKG24AccuracyDiversity.ContinuousSphereConcrete
import dep.PRPKG24AccuracyDiversity.Exchange
import dep.PRPKG24AccuracyDiversity.GeneralRounding
import dep.PRPKG24AccuracyDiversity.Representation
import dep.PRPKG24AccuracyDiversity.SeparableAsymptotic
import dep.PRPKG24AccuracyDiversity.TopKOracle
import dep.PRPKG24AccuracyDiversity.Uniform

open scoped BigOperators

open Filter MeasureTheory

namespace PRPKG24AccuracyDiversity

namespace PaperInterface

/--
Proposition 4: two-measure symmetry-driven kernel endpoint with the
positive-Laplace bridge exposed.

Source status: formalized
Source note: the generic positive-Laplace step is Lean-proved through the
large-deviation library. The paper-facing endpoint is specialized to a unit
sphere and log radial-distance kernel; Lean proves the linear-isometry action,
measurable-embedding, diagonal radial-kernel invariance, sphere transitivity,
normalized Haar-sphere measure preservation, uniform-profile objective value,
and compact-sphere maximizer. The strongest endpoint fixes the ambient Haar
measure to mathlib's finite-dimensional inner-product-space volume, takes
relaxed profiles to be literal probability measures on the unit sphere, defines
the profile objective as the user supremum, and derives the needed continuity
and integrability facts from compactness plus joint continuity of the kernel.
The exposed source-shaped wrapper retains the paper's nonconstant `(0,1]`
radial-kernel condition on the realized unit-sphere distance range `[0,2]`.
It also exposes continuity of the radial function, the minor analytic
regularity needed by the exact compact-sphere Laplace limit.  The conclusion
corrects the printed type error `Gamma(pi) in inf_alpha Gamma(alpha)` to the
intended pointwise minimization inequality.  Equations (17) and (20) are
exposed separately above as the exact bridge from the source limit to this
compact-supremum objective.
-/
theorem proposition4
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace (Proposition4Sphere.UnitSphere E)]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (preferenceMeasure : MeasureTheory.Measure (Proposition4Sphere.UnitSphere E))
    [MeasureTheory.IsProbabilityMeasure preferenceMeasure]
    (p : ℝ → ℝ)
    (hopen : MeasureTheory.Measure.IsOpenPosMeasure preferenceMeasure)
    (hp : Continuous p)
    (hp_nonconstant :
      ∃ r ∈ Set.Icc (0 : ℝ) 2,
        ∃ s ∈ Set.Icc (0 : ℝ) 2, p r ≠ p s)
    (hp_range :
      ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 2 → 0 < p r ∧ p r ≤ 1) :
    ∀ alpha : MeasureTheory.ProbabilityMeasure (Proposition4Sphere.UnitSphere E),
      Proposition4Sphere.logRadialDistanceProfileSupValue (E := E) p
          (Proposition4Sphere.sphereVolumeUniformProbabilityMeasure (E := E)) ≤
        Proposition4Sphere.logRadialDistanceProfileSupValue (E := E) p alpha := sorry

end PaperInterface

end PRPKG24AccuracyDiversity
