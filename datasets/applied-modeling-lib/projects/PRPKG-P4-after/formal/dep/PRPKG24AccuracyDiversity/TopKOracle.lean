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
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
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
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Probability.CDF
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.ProjIcc
import dep.AppliedModelingLib.Applications.RecommenderSystems.Allocation
import dep.AppliedModelingLib.Foundations.Math.Asymptotics
import dep.AppliedModelingLib.Foundations.Probability.OrderStatistics
import dep.AppliedModelingLib.Foundations.Probability.PMFKernel
import dep.PRPKG24AccuracyDiversity.Basic

open scoped BigOperators

namespace PRPKG24AccuracyDiversity

/--
Oracle for the expected value of the best `ℓ` consumed items among `q` recommendations
of a single type.

This file intentionally keeps order statistics abstract. It is the right interface for
Theorem 1 of the paper: later files can instantiate this oracle for finite-discrete,
bounded, exponential-tail, or heavy-tail conditional item-value distributions.
-/
abbrev TopKValueOracle (T : ℕ) :=
  AppliedModelingLib.Probability.TopKExpectationOracle (ItemType T)

namespace TopKValueOracle

/-- Build a consumption model for a fixed consumption constraint `ℓ`. -/
def toConsumptionModel {T : ℕ}
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (ℓ : ℕ) : ConsumptionModel T where
  likelihood := likelihood
  valueOfCount := fun t q => O.expectedTopSum ℓ t q

/-- Marginal top-`ℓ` value from adding one more recommendation of type `t`. -/
def marginalTopK {T : ℕ}
    (O : TopKValueOracle T) (ℓ : ℕ) (t : ItemType T) (q : ℕ) : ℝ :=
  O.expectedTopSum ℓ t (q + 1) - O.expectedTopSum ℓ t q

end TopKValueOracle

end PRPKG24AccuracyDiversity
