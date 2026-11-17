import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.AffineSpace.Ordered
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue
import dep.EconCSLib.Foundations.Probability.FiniteExpectation
import dep.EconCSLib.Foundations.Probability.FiniteProductMultinomialCounts
import dep.EconCSLib.Foundations.Probability.FiniteRankingEvents
import dep.EconCSLib.Foundations.Probability.FiniteRatingComparison
import dep.EconCSLib.Foundations.Probability.FiniteSupportMGF
import dep.EconCSLib.Foundations.Probability.IIDLargeDeviations
import dep.EconCSLib.Foundations.Probability.IndependentProduct
import dep.EconCSLib.Foundations.Probability.IntegralLargeDeviations
import dep.EconCSLib.Foundations.Probability.LargeDeviations

open scoped BigOperators

open MeasureTheory

namespace EconCSLib

namespace Probability

noncomputable section

/-- Bernoulli finite law from a real success probability in `[0,1]`. -/
def realBernoulliPMF (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : PMF Bool :=
  PMF.bernoulli ⟨p, hp0⟩ (sorry)

/-- Binary rating score: success has score `1`, failure has score `0`. -/
def binaryRatingScore (b : Bool) : ℝ :=
  if b then 1 else 0

/-- Failure-side weighted geometric base for two Bernoulli probabilities. -/
def weightedBernoulliFailureBase (gHi gLo pHi pLo : ℝ) : ℝ :=
  (1 - pLo) ^ (gLo / (gHi + gLo)) *
    (1 - pHi) ^ (gHi / (gHi + gLo))

/-- Success-side weighted geometric base for two Bernoulli probabilities. -/
def weightedBernoulliSuccessBase (gHi gLo pHi pLo : ℝ) : ℝ :=
  pLo ^ (gLo / (gHi + gLo)) *
    pHi ^ (gHi / (gHi + gLo))

/-- Closed-rate base for the weighted two-Bernoulli threshold problem. -/
def weightedBernoulliClosedRateBase (gHi gLo pHi pLo : ℝ) : ℝ :=
  weightedBernoulliFailureBase gHi gLo pHi pLo +
    weightedBernoulliSuccessBase gHi gLo pHi pLo

/-- Closed weighted two-Bernoulli threshold rate. -/
def weightedBernoulliClosedThresholdRate (gHi gLo pHi pLo : ℝ) : ℝ :=
  -(gHi + gLo) *
    Real.log (weightedBernoulliClosedRateBase gHi gLo pHi pLo)

/-- `Bool`-valued finite-rating LDP model from real success probabilities. -/
def realBinaryRatingLDPModel {θ : Type*}
    (successProb : θ → ℝ)
    (hprob0 : ∀ t, 0 ≤ successProb t)
    (hprob1 : ∀ t, successProb t ≤ 1) :
    FiniteRatingLDPModel θ Bool where
  typeLaw := fun t => realBernoulliPMF (successProb t) (hprob0 t) (hprob1 t)
  score := binaryRatingScore

end

end Probability

end EconCSLib
