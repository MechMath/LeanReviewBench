import Cslib.Foundations.Data.RelatesInSteps
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Count
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Find
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.GroupTheory.Perm.List
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.WellFoundedSet
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.Order.Compact
import dep.EconCSLib.Foundations.Probability.FairCoin
import dep.EconCSLib.Foundations.Probability.FiniteExpectation
import dep.EconCSLib.MechanismDesign.Auctions.Combinatorial
import dep.EconCSLib.MechanismDesign.Auctions.DigitalGoods
import dep.EconCSLib.MechanismDesign.Auctions.Position
import dep.EconCSLib.SocialChoice.FairDivision.IndivisibleGoods

open MeasureTheory

open ProbabilityTheory

namespace EconCSLib

namespace Auction

/-- Paper Definition: The revenue of a digital goods auction outcome.
    $\sum_{i \in \text{winners}} p_i$
-/
noncomputable def paper_digital_goods_revenue {Agent : Type*} [Fintype Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) : ℝ :=
  ∑ i : Agent, M.payment values i

theorem paper_digital_goods_revenue_eq {Agent : Type*} [Fintype Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) :
    paper_digital_goods_revenue M values = M.revenue values := sorry

/-- Paper Definition: Dominant Strategy Truthful (DSIC).
    $v_i x_i(v_i, b_{-i}) - p_i(v_i, b_{-i}) \ge v_i x_i(b_i, b_{-i}) - p_i(b_i, b_{-i})$
-/
def paper_digital_goods_truthful {Agent : Type*} [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent) : Prop :=
  ∀ (values : Agent → ℝ) (i : Agent) (report : ℝ),
    M.utility values i (Function.update values i report) ≤
      M.utility values i values

theorem paper_digital_goods_truthful_eq {Agent : Type*} [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent) :
    paper_digital_goods_truthful M ↔ M.TruthfulDominantStrategy := sorry

/-- Paper Definition: Two-winner Fixed Price Benchmark $\mathcal{F}^{(2)}(v)$.
    The maximum revenue obtainable from a single price that sells to at least two bidders.
-/
noncomputable def paper_two_winner_benchmark {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) : ℝ :=
  twoWinnerFixedPriceBenchmarkValue values

theorem paper_two_winner_benchmark_eq {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) :
    paper_two_winner_benchmark values = twoWinnerFixedPriceBenchmarkValue values := sorry

/--
Posted-price digital-goods auctions are dominant-strategy truthful.
-/
theorem paper_posted_price_truthful
    {Agent : Type*} [DecidableEq Agent] (price : Agent → ℝ) :
    paper_digital_goods_truthful (postedPrice price) := sorry

/--
Posted-price digital-goods auctions are individually rational.
-/
theorem paper_posted_price_individually_rational
    {Agent : Type*} (price : Agent → ℝ) :
    (postedPrice price).IndividuallyRational := sorry

/--
Posted-price digital-goods auctions have no positive transfers when all prices
are nonnegative.
-/
theorem paper_posted_price_no_positive_transfers
    {Agent : Type*} (price : Agent → ℝ) (hprice : ∀ i, 0 ≤ price i) :
    (postedPrice price).NoPositiveTransfers := sorry

/--
For a fixed anonymous posted price, digital-goods auction revenue is the
single-price revenue benchmark expression.
-/
theorem paper_posted_price_revenue_eq_single_price
    {Agent : Type*} [Fintype Agent] (values : Agent → ℝ) (p : ℝ) :
    (postedPrice fun _ : Agent => p).revenue values =
      singlePriceRevenue values p := sorry

/--
Own-bid-independent threshold-price digital-goods auctions are
dominant-strategy truthful.
-/
theorem paper_threshold_price_truthful
    {Agent : Type*} [DecidableEq Agent]
    (threshold : (Agent → ℝ) → Agent → ℝ)
    (hind : OwnBidIndependent threshold) :
    paper_digital_goods_truthful (thresholdPriceAuction threshold) := sorry

/--
If a digital-goods offer price is computed after erasing the bidder's own bid,
the resulting threshold-price auction is dominant-strategy truthful.
-/
theorem paper_own_erased_threshold_price_truthful
    {Agent : Type*} [DecidableEq Agent]
    (priceRule : Agent → (Agent → ℝ) → ℝ) :
    paper_digital_goods_truthful (thresholdPriceAuction (ownErasedThreshold priceRule)) := sorry

/--
GHW Theorem 6.2 measure-theoretic probability-combination step. This is the
same union-bound endpoint as `paper_theorem6_2_random_sampling_union_bound`,
but for product measures such as independent fair half-sampling.
-/
theorem paper_theorem6_2_random_sampling_measure_union_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (sampleGood revenueGood target : Set Ω)
    (hsample_meas : MeasurableSet sampleGood)
    (hrevenue_meas : MeasurableSet revenueGood)
    {epsSample epsRevenue : ℝ}
    (hsample : 1 - epsSample ≤ μ.real sampleGood)
    (hrevenue : 1 - epsRevenue ≤ μ.real revenueGood)
    (himp : sampleGood ∩ revenueGood ⊆ target) :
    1 - epsSample - epsRevenue ≤ μ.real target := sorry

/--
GHW Lemma 6.1-style relaxed half-sampling endpoint for independent fair
coins. This is stated with the paper's `exp(-|S|/36)` constant; the reusable
library proof establishes the slightly stronger Hoeffding exponent first.
-/
theorem paper_aux_theorem6_2_fair_coin_lower_tail_relaxed
    {Index : Type*} (s : Finset Index) (keep : Bool) :
    (FairCoin.productMeasure Index).real
        {side | (∑ i ∈ s, if side i = keep then (1 : ℝ) else 0) ≤
          (s.card : ℝ) / 3} ≤
      Real.exp (-(s.card : ℝ) / 36) := sorry

/--
Paper-facing independent fair-coin model for the Lemma 6.1 sampling estimate.
-/
structure PaperLemma61FairCoinModel (Index : Type*) where
  sampleSet : Finset Index
  keep : Bool

/--
GHW Lemma 6.1 independent fair-coin paper-model form. A fixed bidder set has
at most `exp(-|S|/36)` probability of contributing at most one third of its
members to a chosen fair-coin side.
-/
theorem paper_lemma6_1_fair_coin_lower_tail_of_model
    {Index : Type*} (model : PaperLemma61FairCoinModel Index) :
    (FairCoin.productMeasure Index).real
        {side |
          (∑ i ∈ model.sampleSet,
            if side i = model.keep then (1 : ℝ) else 0) ≤
          (model.sampleSet.card : ℝ) / 3} ≤
      Real.exp (-(model.sampleSet.card : ℝ) / 36) := sorry

/--
GHW Theorem 6.2 ranked finite-candidate benchmark form without a separate
large-`alpha` side condition. Small `alpha` is discharged by the nonpositive
probability lower bound above, and the top-prefix family is ranked internally.
-/
theorem paper_theorem6_2_fair_coin_revenue_bound_of_finite_candidate_benchmark_all_alpha
    {n : ℕ} [NeZero n] (values : Fin n → ℝ) (keep : Bool)
    {alpha : ℕ} {highValue : ℝ}
    (hhigh_pos : 0 < highValue)
    (hvalue_bound : ∀ i, values i ≤ highValue)
    (halpha_highValue :
      (alpha : ℝ) * highValue ≤
        finiteCandidateFixedPriceBenchmark values 1) :
    1 - Real.exp (-(alpha : ℝ) / 36) -
        40 * Real.exp (-(alpha : ℝ) / 72) ≤
      (FairCoin.productMeasure (Fin n)).real
        {side |
          finiteCandidateFixedPriceBenchmark values 1 ≤
            6 *
              (thresholdPriceAuction
                (crossSampleCandidateOfferThreshold side 1)).revenue values} := sorry

/--
The finite bidder-value candidate benchmark is nonnegative.
-/
theorem paper_finite_candidate_fixed_price_benchmark_nonneg
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (minWinners : ℕ) :
    0 ≤ finiteCandidateFixedPriceBenchmark values minWinners := sorry

/--
Any feasible nonnegative fixed price with at least one required winner is
dominated by the finite bidder-value candidate benchmark.
-/
theorem paper_single_price_revenue_le_candidate_benchmark_of_feasible
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) {minWinners : ℕ} {p : ℝ}
    (hmin : 1 ≤ minWinners)
    (hp : 0 ≤ p)
    (hfeasible : minWinners ≤ saleCount values p) :
    singlePriceRevenue values p ≤
      finiteCandidateFixedPriceBenchmark values minWinners := sorry

/--
If there is at least one feasible two-winner fixed price, the finite
bidder-value candidate benchmark is the `F^(2)` fixed-price benchmark.
-/
theorem paper_two_winner_fixed_price_benchmark
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ)
    (hexists : ∃ p, 0 ≤ p ∧ 2 ≤ saleCount values p) :
    IsTwoWinnerFixedPriceBenchmark values
      (finiteCandidateFixedPriceBenchmark values 2) := sorry

/--
Rounded dyadic auxiliary bound for normalized bids in `[1,h]`.  The additive
term pays for integer bin rounding; it is retained for internal callers and
is not the exact printed Theorem 4.1 endpoint.
-/
theorem paper_theorem4_1_finite_candidate_benchmark_from_logb_high_value
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) {h : ℝ}
    (hh_ge_one : 1 ≤ h)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h) :
    totalBidValue values ≤
      (2 * (Real.logb 2 h + 2)) *
        finiteCandidateFixedPriceBenchmark values 1 := sorry

/-- Corrected exact GHW Theorem 4.1 endpoint.  The printed source statement
needs the visible restriction `2 <= h`; without it the real-log denominator
can be too small. -/
theorem paper_theorem4_1_finite_candidate_benchmark_exact_logb_of_two_le
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) {h : ℝ}
    (hh_ge_two : 2 ≤ h)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h) :
    totalBidValue values ≤
      (2 * Real.logb 2 h) * finiteCandidateFixedPriceBenchmark values 1 := sorry

/--
Paper-facing normalized high-value model for GHW Theorem 4.1. It packages the
finite formalization's normalized bidder values in `[1,h]`.
-/
structure PaperTheorem41HighValueModel
    (Agent : Type*) [Fintype Agent] [Nonempty Agent] [DecidableEq Agent] where
  values : Agent → ℝ
  highValue : ℝ
  highValue_ge_one : 1 ≤ highValue
  values_ge_one : ∀ i : Agent, 1 ≤ values i
  values_le_highValue : ∀ i : Agent, values i ≤ highValue

/-- Rounded high-value model consequence used by the dyadic helper route. -/
theorem paper_theorem4_1_finite_candidate_benchmark_of_high_value_model
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (model : PaperTheorem41HighValueModel Agent) :
    totalBidValue model.values ≤
      (2 * (Real.logb 2 model.highValue + 2)) *
        finiteCandidateFixedPriceBenchmark model.values 1 := sorry

/--
GHW Corollary 4.2 with the paper truncation constructed internally. If `h`
is the highest bid value, retaining bids at least `h / n` and normalizing by
that cutoff gives a `[1,n]` high-value instance, so Theorem 4.1 yields the
factor-four logarithmic fixed-price lower bound.
-/
theorem paper_corollary4_2_fixed_price_lower_bound_of_card_truncation
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) {h binCount : ℝ}
    (hvalues_nonneg : ∀ i : Agent, 0 ≤ values i)
    (hh_pos : 0 < h)
    (hmax : ∃ i : Agent, values i = h)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hbinCount : Real.logb 2 (Fintype.card Agent : ℝ) + 2 ≤ binCount) :
    totalBidValue values ≤
      (4 * binCount) * finiteCandidateFixedPriceBenchmark values 1 := sorry

/--
Corrected exact GHW Corollary 4.2 endpoint.  The printed real-log denominator
requires the visible nondegenerate cardinality condition `2 <= n`.
-/
theorem paper_corollary4_2_fixed_price_lower_bound_exact_logb_of_card_two_le
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) {h : ℝ}
    (hvalues_nonneg : ∀ i : Agent, 0 ≤ values i)
    (hh_pos : 0 < h)
    (hmax : ∃ i : Agent, values i = h)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hcard_ge_two : 2 ≤ (Fintype.card Agent : ℝ)) :
    totalBidValue values ≤
      (4 * Real.logb 2 (Fintype.card Agent : ℝ)) *
        finiteCandidateFixedPriceBenchmark values 1 := sorry

/--
GHW Theorem 7.1 rounded `log_2 h` form. If bids lie in `[1,h]`, `1 <= h`,
and the total value satisfies the paper large-market condition (`4h <= T`),
then the weighted-pairing revenue satisfies the paper-style logarithmic bound
with `log_2 h + 2`.
-/
theorem paper_theorem7_1_weighted_pairing_log_bound_from_logb_high_value
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) {h totalValue : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hh_ge_one : 1 ≤ h)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hlarge : 4 * h ≤ totalValue) :
    totalValue ≤
      192 * (Real.logb 2 h + 2) *
        weightedPairingExpectedRevenue values := sorry

/--
Paper-facing high-value model for GHW Theorem 7.1. The rounded dyadic endpoint
uses relative factor-two bins, so the large-market hypothesis is the paper
condition `4h <= T`; the logarithmic coefficient remains rounded as
`log_2 h + 2`.
-/
structure PaperTheorem71WeightedPairingHighValueModel
    (Agent : Type*) [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent] where
  values : Agent → ℝ
  highValue : ℝ
  totalValue : ℝ
  total_value_eq : totalValue = totalBidValue values
  highValue_ge_one : 1 ≤ highValue
  values_ge_one : ∀ i : Agent, 1 ≤ values i
  values_le_highValue : ∀ i : Agent, values i ≤ highValue
  large_market : 4 * highValue ≤ totalValue

/--
GHW Theorem 7.1 high-value paper-model form: under the rounded dyadic
high-value model, weighted pairing obtains the logarithmic revenue bound.
-/
theorem paper_theorem7_1_weighted_pairing_log_bound_of_high_value_model
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (model : PaperTheorem71WeightedPairingHighValueModel Agent) :
    model.totalValue ≤
      192 * (Real.logb 2 model.highValue + 2) *
        weightedPairingExpectedRevenue model.values := sorry

/--
GHW Theorem 7.2 for the finite two-winner fixed-price benchmark `F^(2)`.
This is the paper-facing form of the lower bound: with all values normalized to
`[1, 2^(m+1)]`, if `F^(2) >= 2h` and `m+1 <= s^2`, then the weighted-pairing
auction earns a `1 / O(s)` fraction of `F^(2)`.
-/
theorem paper_theorem7_2_weighted_pairing_bound_for_two_winner_benchmark
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (values : Agent → ℝ) (m : ℕ)
    {totalValue s : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_power : ∀ i : Agent, values i ≤ (2 : ℝ) ^ (m + 1))
    (hF_ge_two_power :
      2 * (2 : ℝ) ^ (m + 1) ≤ twoWinnerFixedPriceBenchmarkValue values)
    (hs_ge_two : 2 ≤ s)
    (hlog_le_s_sq : ((m + 1 : ℕ) : ℝ) ≤ s ^ 2) :
    twoWinnerFixedPriceBenchmarkValue values ≤
      576 * s * weightedPairingExpectedRevenue values := sorry

/--
GHW Theorem 7.2 rounded `log_2 h` form for the finite two-winner benchmark.
The side condition is the paper high-value condition `F^(2) >= 2h`; only the
logarithmic coefficient is rounded as `log_2 h + 2`.
-/
theorem paper_theorem7_2_weighted_pairing_bound_for_two_winner_benchmark_from_logb_high_value
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (values : Agent → ℝ) {h totalValue s : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hh_ge_one : 1 ≤ h)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hF_ge_two_h :
      2 * h ≤ twoWinnerFixedPriceBenchmarkValue values)
    (hs_ge_two : 2 ≤ s)
    (hlog_le_s_sq : Real.logb 2 h + 2 ≤ s ^ 2) :
    twoWinnerFixedPriceBenchmarkValue values ≤
      576 * s * weightedPairingExpectedRevenue values := sorry

/--
Paper-facing high-value model for GHW Theorem 7.2. The rounded dyadic endpoint
uses the paper condition `F^(2) >= 2h`; the logarithmic coefficient remains
rounded as `log_2 h + 2`.
-/
structure PaperTheorem72WeightedPairingHighValueModel
    (Agent : Type*) [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent] where
  values : Agent → ℝ
  highValue : ℝ
  totalValue : ℝ
  scale : ℝ
  total_value_eq : totalValue = totalBidValue values
  highValue_ge_one : 1 ≤ highValue
  values_ge_one : ∀ i : Agent, 1 ≤ values i
  values_le_highValue : ∀ i : Agent, values i ≤ highValue
  benchmark_large :
    2 * highValue ≤ twoWinnerFixedPriceBenchmarkValue values
  scale_ge_two : 2 ≤ scale
  log_le_scale_sq : Real.logb 2 highValue + 2 ≤ scale ^ 2

/--
GHW Theorem 7.2 high-value paper-model form: under the rounded dyadic
high-value model, the weighted-pairing revenue gives the two-winner benchmark
bound.
-/
theorem paper_theorem7_2_weighted_pairing_bound_for_two_winner_benchmark_of_high_value_model
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (model : PaperTheorem72WeightedPairingHighValueModel Agent) :
    twoWinnerFixedPriceBenchmarkValue model.values ≤
      576 * model.scale * weightedPairingExpectedRevenue model.values := sorry

/--
Lower-level bidders in the GHW Theorem 7.2 tightness family. Level `r`
represents value `2^(r+1)` and contains `2^(k-(r+1))` repeated bids.
-/
abbrev GhwTightLowerAgent (k : ℕ) :=
  Sigma fun r : Fin (k - 1) => Fin (2 ^ (k - (r.val + 1)))

/-- The full GHW Theorem 7.2 tightness family: lower levels plus `s` top bids. -/
abbrev GhwTightAgent (k s : ℕ) := GhwTightLowerAgent k ⊕ Fin s

/-- Bid values in the GHW Theorem 7.2 tightness family. -/
noncomputable def ghwTightValue (k s : ℕ) : GhwTightAgent k s → ℝ
  | Sum.inl a => (2 : ℝ) ^ (a.1.val + 1)
  | Sum.inr _ => (2 : ℝ) ^ k

/--
The actual two-winner fixed-price benchmark for the GHW tightness family.
The proof `2 <= s` supplies the nonempty top block needed by the finite
candidate benchmark API.
-/
noncomputable def ghwTightTwoWinnerBenchmarkValue
    (k s : ℕ) (hs_two : 2 ≤ s) : ℝ :=
  have hs_pos : 0 < s := sorry
  haveI : Nonempty (GhwTightAgent k s) :=
    ⟨Sum.inr ⟨0, hs_pos⟩⟩
  twoWinnerFixedPriceBenchmarkValue (ghwTightValue k s)

/--
GHW Theorem 7.2 tightness endpoint for the repeated-bid family. For `s` top
bids of value `2^k` and lower levels containing `2^(k-r)` copies of value
`2^r`, the weighted-pairing auction earns at most `(3/s)` times the actual
two-winner fixed-price benchmark.
-/
theorem paper_theorem7_2_tightness_ratio_for_repeated_bid_family
    (k s : ℕ) (hs_two : 2 ≤ s)
    (hk_large : s * s + 2 ≤ k) :
    weightedPairingExpectedRevenue (ghwTightValue k s) ≤
      (3 / (s : ℝ)) *
        ghwTightTwoWinnerBenchmarkValue k s hs_two := sorry

/--
GHW Lemma 8.1, direct-revelation form: in a truthful digital-goods auction,
holding other reports fixed, increasing bidder `i`'s own bid weakly increases
that bidder's allocation probability/quantity.
-/
theorem paper_lemma8_1_allocation_mono_own_bid_of_truthful
    {Agent : Type*} [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent)
    (hM : paper_digital_goods_truthful M)
    (bids : Agent → ℝ) (i : Agent) {low high : ℝ} (hlt : low < high) :
    M.allocation (Function.update bids i low) i ≤
      M.allocation (Function.update bids i high) i := sorry

/--
Expected revenue of the journal-version raw marginal offer laws. For each
bidder `i`, `offerLaw i` is the finite law of that bidder's offer price.
-/
noncomputable def paper_theorem8_2_raw_cdf_expected_revenue
    {Agent Price : Type*} [Fintype Agent] [Fintype Price] [DecidableEq Price]
    (values : Agent → ℝ) (price : Price → ℝ)
    (offerLaw : Agent → PMF Price) : ℝ :=
  ∑ i : Agent,
    pmfExp (offerLaw i) fun p =>
      if price p ≤ values i then price p else 0

/--
Journal-version source model for GHW Theorem 8.2 with raw marginal offer CDF
monotonicity. This is the source-facing finite form of the journal correction:
higher values have weakly larger offer-acceptance CDFs below each lower value.
-/
structure PaperTheorem82JournalRawCDFMonotoneOfferSourceModel
    (Agent Price : Type*) [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent] [Fintype Price] [DecidableEq Price] where
  values : Agent → ℝ
  price : Price → ℝ
  offerLaw : Agent → PMF Price
  value_nonneg : ∀ i, 0 ≤ values i
  price_nonneg : ∀ p, 0 ≤ price p
  cdf_monotone :
    ∀ i j, values i ≤ values j → ∀ t, t ≤ values i →
      pmfProb (offerLaw i) (fun p => price p ≤ t) ≤
        pmfProb (offerLaw j) (fun p => price p ≤ t)

/--
Journal-version GHW Theorem 8.2 from raw CDF monotone marginal offer laws.

The proof works directly with the finite marginal laws. The CDF monotonicity
assumption gives adjacent ranked acceptance-probability monotonicity and,
through a finite layer-cake argument, the adjacent surplus recursion used by
the paper's Theorem 8.2 algebra.
-/
theorem
    paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_raw_cdf_monotone_offer_source_model
    {Agent Price : Type*} [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent] [LinearOrder Agent] [Fintype Price] [DecidableEq Price]
    (model : PaperTheorem82JournalRawCDFMonotoneOfferSourceModel Agent Price) :
    paper_theorem8_2_raw_cdf_expected_revenue
        model.values model.price model.offerLaw ≤
      finiteCandidateFixedPriceBenchmark model.values 1 := sorry

/--
GHW Theorem 9.1 bid-independent-function form. For an arbitrary anonymous
paper-style price rule `f` on erased bid lists, restrict `f` to canonical
two-value lists and apply the binary adversarial construction.
-/
theorem paper_theorem9_1_bid_independent_list_rule_scaled_lower_bound_fixed_price_benchmark
    (priceRule : List ℝ → ℝ) {highValue alpha : ℕ}
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (highValue : ℝ) *
          twoValueBidIndependentPriceRevenue
            (twoValueListBidIndependentThresholdPrice priceRule highValue)
            highValue highCount lowCount ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := sorry

/--
GHW Lemma 9.2 auction-level threshold-domination form. After fixing other bids,
a truthful, individually rational, no-positive-transfers deterministic auction
has a nonnegative threshold that dominates the bidder's payment slice.
-/
theorem paper_lemma9_2_deterministic_truthful_auction_exists_nonnegative_threshold_dominates
    {Agent : Type*} [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent)
    (htruth : paper_digital_goods_truthful M)
    (hIR : M.IndividuallyRational)
    (hNPT : M.NoPositiveTransfers)
    (hbinary : M.BinaryAllocation)
    (bids : Agent → ℝ) (i : Agent) :
    ∃ threshold,
      0 ≤ threshold ∧
        DeterministicOfferThresholdDominates
          (deterministicAuctionOffer M bids i) threshold := sorry

/--
The anonymous erased bid list seen by a bidder in a two-value profile. High and
low bidders are stored in separate finite blocks, and the target bidder's own
coordinate is erased from the appropriate block.
-/
def paper_theorem9_3_erased_report_list {highCount lowCount : ℕ}
    (bids : TwoValueAgent highCount lowCount → ℝ)
    (i : TwoValueAgent highCount lowCount) : List ℝ :=
  match i with
  | Sum.inl i =>
      (List.ofFn fun j : Fin highCount => bids (Sum.inl j)).eraseIdx (i : ℕ) ++
        (List.ofFn fun j : Fin lowCount => bids (Sum.inr j))
  | Sum.inr i =>
      (List.ofFn fun j : Fin highCount => bids (Sum.inl j)) ++
        (List.ofFn fun j : Fin lowCount => bids (Sum.inr j)).eraseIdx (i : ℕ)

/--
Primitive erased-bid-list offer auction for GHW Theorem 9.3. The offer rule
sees the anonymous erased bid list and the bidder's report, returning either a
posted price (`some price`) or rejection (`none`).
-/
noncomputable def paper_theorem9_3_bid_list_offer_auction
    (offerRule : List ℝ → ℝ → Option ℝ)
    (highCount lowCount : ℕ) :
    DigitalGoodsAuction (TwoValueAgent highCount lowCount) where
  allocation bids i :=
    match offerRule (paper_theorem9_3_erased_report_list bids i) (bids i) with
    | some _ => 1
    | none => 0
  payment bids i :=
    match offerRule (paper_theorem9_3_erased_report_list bids i) (bids i) with
    | some price => price
    | none => 0

end Auction

end EconCSLib

namespace GHW01DigitalGoods

namespace Theorem93

open EconCSLib.Auction

/--
Primitive set-of-bids source model for GHW Theorem 9.3. The paper writes a
deterministic auction as mapping a set of bids to outcomes and, in Lemma 9.2,
studies the focused slice `A_i(B_i^x)`. The `focusedOutcome` field is that
anonymous erased-bid-multiset slice: `none` means rejection, and `some price`
means satisfied at that price.  Repeated bid values are retained, but the
source-facing field cannot inspect their presentation order or bidder labels.
-/
structure PaperTheorem93PrimitiveSetOfBidsDeterministicSourceModel
    (_highValue : ℕ) where
  auctionFamily :
    ∀ highCount lowCount,
      DigitalGoodsAuction (TwoValueAgent highCount lowCount)
  truthful :
    ∀ highCount lowCount,
      paper_digital_goods_truthful (auctionFamily highCount lowCount)
  binary :
    ∀ highCount lowCount,
      (auctionFamily highCount lowCount).BinaryAllocation
  individuallyRational :
    ∀ highCount lowCount,
      (auctionFamily highCount lowCount).IndividuallyRational
  noPositiveTransfers :
    ∀ highCount lowCount,
      (auctionFamily highCount lowCount).NoPositiveTransfers
  focusedOutcome : Multiset ℝ → ℝ → Option ℝ
  focusedOutcome_represents :
    ∀ {highCount lowCount : ℕ}
      (bids : TwoValueAgent highCount lowCount → ℝ)
      (i : TwoValueAgent highCount lowCount),
      deterministicAuctionOffer
          (auctionFamily highCount lowCount) bids i =
        focusedOutcome
          (Multiset.ofList (paper_theorem9_3_erased_report_list bids i))

/--
Paper-local primitive erased-bid-list offer model for GHW Theorem 9.3. Instead
of assuming an already packaged auction family plus erased-list factorization,
the model starts from the paper-style anonymous offer rule itself.
-/
structure PrimitiveErasedBidOfferModel
    (_highValue : ℕ) where
  offerRule : List ℝ → ℝ → Option ℝ
  offer_truthful :
    ∀ erasedBids, DeterministicOfferTruthful (offerRule erasedBids)
  offer_feasible :
    ∀ erasedBids, DeterministicOfferFeasible (offerRule erasedBids)
  offer_price_nonnegative :
    ∀ erasedBids report price,
      offerRule erasedBids report = some price → 0 ≤ price

end Theorem93

end GHW01DigitalGoods

namespace EconCSLib

namespace Auction

open GHW01DigitalGoods.Theorem93

/--
GHW Theorem 9.3 source-model form using the paper's primitive set-of-bids
focused-outcome convention. The global erased-list relabeling bridge is
derived internally from the focused outcome representation before Lemma 9.2
constructs representative prices.
-/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_primitive_set_of_bids_source_model
    {highValue alpha : ℕ}
    (sourceModel :
      PaperTheorem93PrimitiveSetOfBidsDeterministicSourceModel highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (sourceModel.auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount) /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := sorry

/--
GHW Theorem 9.3 source-model form from the primitive anonymous erased-bid-list
offer rule. This is the strongest current source-level bridge: the auction
family and erased-list factorization certificate are constructed internally.
-/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_primitive_bid_list_offer_source_model
    {highValue alpha : ℕ}
    (sourceModel :
      GHW01DigitalGoods.Theorem93.PrimitiveErasedBidOfferModel highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      ((paper_theorem9_3_bid_list_offer_auction
          sourceModel.offerRule highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount)) /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := sorry

end Auction

end EconCSLib
