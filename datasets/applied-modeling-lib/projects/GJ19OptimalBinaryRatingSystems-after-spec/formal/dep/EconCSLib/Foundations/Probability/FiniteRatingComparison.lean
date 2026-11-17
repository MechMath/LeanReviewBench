import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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
import Mathlib.Tactic.Ring
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import dep.EconCSLib.Foundations.Probability.FiniteExpectation
import dep.EconCSLib.Foundations.Probability.FiniteProductMultinomialCounts
import dep.EconCSLib.Foundations.Probability.FiniteRankingEvents
import dep.EconCSLib.Foundations.Probability.FiniteSupportMGF
import dep.EconCSLib.Foundations.Probability.IIDLargeDeviations
import dep.EconCSLib.Foundations.Probability.IndependentProduct
import dep.EconCSLib.Foundations.Probability.IntegralLargeDeviations
import dep.EconCSLib.Foundations.Probability.LargeDeviations

open scoped BigOperators

open Filter SignType

namespace EconCSLib

namespace Probability

noncomputable section

/--
A seller type's finite rating law places positive mass on both sides of a
threshold score. This is the nondegeneracy condition used by the finite
empirical-type Cramer lower bound.
-/
def ratingLawStraddlesThreshold
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (θ : Seller) (a : ℝ) : Prop :=
  M.straddlesThreshold θ a

/--
Appendix pairwise threshold rate for comparing two seller types.  This is the
right-hand side of Lemma C.1 / Lemma C.2 before the analytic LDP certificate is
supplied.
-/
def pairwiseSellerThresholdRate {Seller Rating : Type*} [Fintype Rating]
    [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) : ℝ :=
  M.pairwiseThresholdRate sampleRate hi lo

/--
Pairwise regularity package for the threshold-rate step. It records exactly the
remaining finite-model data needed to turn every finite floor-count pairwise
comparison into an exact exponential-rate certificate at the real threshold
rate.
-/
structure PairwiseThresholdRateRegularity
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller) where
  threshold : Pair → ℝ
  dual : Pair → ℝ
  dual_nonpos : ∀ p : Pair, dual p ≤ 0
  deriv_hi :
    ∀ p : Pair,
      HasDerivAt (fun t : ℝ => M.logMGF (pairHi p) t) (threshold p)
        (dual p * (sampleRate (pairHi p))⁻¹)
  deriv_lo :
    ∀ p : Pair,
      HasDerivAt (fun t : ℝ => M.logMGF (pairLo p) t) (threshold p)
        (-(dual p * (sampleRate (pairLo p))⁻¹))
  threshold_rate_eq :
    ∀ p : Pair,
      M.pairwiseRateObjective sampleRate (pairHi p) (pairLo p)
          (threshold p) =
        pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)
  straddles_hi :
    ∀ p : Pair, ratingLawStraddlesThreshold M (pairHi p) (threshold p)
  straddles_lo :
    ∀ p : Pair, ratingLawStraddlesThreshold M (pairLo p) (threshold p)

namespace PairwiseThresholdRateRegularity

end PairwiseThresholdRateRegularity

/--
Independent high/low rating samples with possibly different sample counts.
This is the finite object behind the source counts `k g(theta_hi)` and
`k g(theta_lo)`.
-/
noncomputable def twoSampleRatingLaw
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (nHi nLo : ℕ) :
    PMF ((Fin nHi → Rating) × (Fin nLo → Rating)) :=
  EconCSLib.pmfProd
    (EconCSLib.pmfProduct (Fin nHi) Rating (M.typeLaw hi))
    (EconCSLib.pmfProduct (Fin nLo) Rating (M.typeLaw lo))

/-- Scaled high-low sample-score gap for independent finite samples. -/
def twoSampleScoreGapSum
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) {nHi nLo : ℕ}
    (cHi cLo : ℝ)
    (sample : (Fin nHi → Rating) × (Fin nLo → Rating)) : ℝ :=
  cHi * finiteIidScoreSum M.score sample.1 -
    cLo * finiteIidScoreSum M.score sample.2

/-- Strict-left comparison probability for the scaled two-sample score gap. -/
def twoSampleScoreGapStrictLeftProb
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (nHi nLo : ℕ) (cHi cLo : ℝ) : ℝ :=
  EconCSLib.pmfProb (twoSampleRatingLaw M hi lo nHi nLo)
    (fun sample => twoSampleScoreGapSum M cHi cLo sample < 0)

/-- Tie probability for the scaled two-sample score gap. -/
def twoSampleScoreGapTieProb
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (nHi nLo : ℕ) (cHi cLo : ℝ) : ℝ :=
  EconCSLib.pmfProb (twoSampleRatingLaw M hi lo nHi nLo)
    (fun sample => twoSampleScoreGapSum M cHi cLo sample = 0)

/--
Paper `1 - P_k` comparison error for a fixed pair: twice the strict inversion
probability plus the tie probability.
-/
def twoSamplePkComplementErrorProb
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (nHi nLo : ℕ) (cHi cLo : ℝ) : ℝ :=
  2 * twoSampleScoreGapStrictLeftProb M hi lo nHi nLo cHi cLo +
    twoSampleScoreGapTieProb M hi lo nHi nLo cHi cLo

/-- Paper sample count `n_k(theta) = floor(k * g(theta))`. -/
def floorSampleCount {Seller : Type*} (sampleRate : Seller → ℝ)
    (θ : Seller) (k : ℕ) : ℕ :=
  Nat.floor ((k : ℝ) * sampleRate θ)

/--
Source-shaped floor-count `1 - P_k` comparison error for a two-seller pair.
-/
def twoSampleFloorPkComplementErrorProb
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (k : ℕ) : ℝ :=
  let nHi := floorSampleCount sampleRate hi k
  let nLo := floorSampleCount sampleRate lo k
  twoSamplePkComplementErrorProb M hi lo nHi nLo
    ((nHi : ℝ)⁻¹) ((nLo : ℝ)⁻¹)

end

end Probability

end EconCSLib
