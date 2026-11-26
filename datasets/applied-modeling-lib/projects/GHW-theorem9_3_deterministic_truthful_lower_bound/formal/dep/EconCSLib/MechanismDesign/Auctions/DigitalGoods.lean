import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Count
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace EconCSLib

namespace Auction

/--
An unlimited-supply digital-goods auction.

The allocation quantity is represented as a real number so this same interface
can later admit fractional relaxations, lotteries in expectation, or position
auction click-through weights.  For the posted-price theorem below, allocations
are always `0` or `1`.
-/
structure DigitalGoodsAuction (Agent : Type*) where
  allocation : (Agent → ℝ) → Agent → ℝ
  payment : (Agent → ℝ) → Agent → ℝ

namespace DigitalGoodsAuction

variable {Agent : Type*}

/-- Quasilinear utility for a digital-good bidder with value `values i`. -/
def utility (M : DigitalGoodsAuction Agent)
    (values : Agent → ℝ) (i : Agent) (bids : Agent → ℝ) : ℝ :=
  values i * M.allocation bids i - M.payment bids i

/--
Dominant-strategy truthfulness for direct-report single-parameter auctions:
holding other reports fixed, replacing agent `i`'s truthful report by any
`report` cannot improve `i`'s utility.
-/
def TruthfulDominantStrategy [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent) : Prop :=
  ∀ (values : Agent → ℝ) (i : Agent) (report : ℝ),
    M.utility values i (Function.update values i report) ≤
      M.utility values i values

/-- Truthful utility is always nonnegative. -/
def IndividuallyRational (M : DigitalGoodsAuction Agent) : Prop :=
  ∀ (values : Agent → ℝ) (i : Agent), 0 ≤ M.utility values i values

/-- The mechanism never pays money to agents. -/
def NoPositiveTransfers (M : DigitalGoodsAuction Agent) : Prop :=
  ∀ (bids : Agent → ℝ) (i : Agent), 0 ≤ M.payment bids i

/-- Total auction revenue under a bid profile. -/
noncomputable def revenue [Fintype Agent]
    (M : DigitalGoodsAuction Agent) (bids : Agent → ℝ) : ℝ :=
  ∑ i : Agent, M.payment bids i

end DigitalGoodsAuction

variable {Agent : Type*}

/--
An anonymous or personalized take-it-or-leave-it posted-price auction for an
unlimited-supply digital good.
-/
noncomputable def postedPrice (price : Agent → ℝ) : DigitalGoodsAuction Agent where
  allocation bids i := if price i ≤ bids i then 1 else 0
  payment bids i := if price i ≤ bids i then price i else 0

/--
Revenue of a single anonymous posted price against a valuation/bid profile.
For the 2021 digital-goods paper this is the basic fixed-price benchmark term.
-/
noncomputable def singlePriceRevenue [Fintype Agent]
    (values : Agent → ℝ) (p : ℝ) : ℝ :=
  ∑ i : Agent, if p ≤ values i then p else 0

/-- Number of bidders who accept a single price. -/
noncomputable def saleCount [Fintype Agent] (values : Agent → ℝ) (p : ℝ) : ℕ :=
  ((Finset.univ : Finset Agent).filter fun i => p ≤ values i).card

/--
Certificate-style fixed-price benchmark for digital goods.

The Goldberg-Hartline-Wright benchmark is a maximum over prices satisfying
extra sale-count restrictions.  This predicate records the exact upper-bound
property without committing yet to the finite maximizer proof.
-/
def IsFixedPriceBenchmark [Fintype Agent]
    (values : Agent → ℝ) (minWinners : ℕ) (benchmark : ℝ) : Prop :=
  (∃ p, 0 ≤ p ∧ minWinners ≤ saleCount values p ∧
    benchmark = singlePriceRevenue values p) ∧
  ∀ p, 0 ≤ p → minWinners ≤ saleCount values p →
    singlePriceRevenue values p ≤ benchmark

/-- The `F^(2)`-style benchmark interface: one price, at least two winners. -/
def IsTwoWinnerFixedPriceBenchmark [Fintype Agent]
    (values : Agent → ℝ) (benchmark : ℝ) : Prop :=
  IsFixedPriceBenchmark values 2 benchmark

/--
Revenue from using bidder `i`'s value as the candidate single price, with
infeasible prices assigned value `0`.
-/
noncomputable def candidateFixedPriceRevenue [Fintype Agent]
    (values : Agent → ℝ) (minWinners : ℕ) (i : Agent) : ℝ :=
  if 0 ≤ values i ∧ minWinners ≤ saleCount values (values i) then
    singlePriceRevenue values (values i)
  else 0

/--
Finite candidate-price benchmark obtained by maximizing over bidder values.

The full `F^(2)` theorem still needs the paper lemma that a globally optimal
single price may be chosen from a bidder value. This definition provides the
finite maximizer needed once that reduction is proved.
-/
noncomputable def finiteCandidateFixedPriceBenchmark [Fintype Agent]
    [Nonempty Agent] (values : Agent → ℝ) (minWinners : ℕ) : ℝ :=
  (Finset.univ : Finset Agent).sup'
    (sorry)
    (candidateFixedPriceRevenue values minWinners)

theorem exists_candidateFixedPriceRevenue_eq_finiteCandidateFixedPriceBenchmark
    [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (minWinners : ℕ) :
    ∃ i : Agent,
      finiteCandidateFixedPriceBenchmark values minWinners =
        candidateFixedPriceRevenue values minWinners i := sorry

/-- A bidder whose value attains the finite candidate-price benchmark. -/
noncomputable def finiteCandidateBenchmarkBidder [Fintype Agent]
    [Nonempty Agent] (values : Agent → ℝ) (minWinners : ℕ) : Agent :=
  Classical.choose
    (exists_candidateFixedPriceRevenue_eq_finiteCandidateFixedPriceBenchmark
      values minWinners)

/--
Nonnegative offer price extracted from the finite candidate benchmark. If the
selected bidder value is not a feasible nonnegative candidate, use price `0`.
-/
noncomputable def finiteCandidateOfferPrice [Fintype Agent]
    [Nonempty Agent] (values : Agent → ℝ) (minWinners : ℕ) : ℝ :=
  let i := finiteCandidateBenchmarkBidder values minWinners
  if 0 ≤ values i ∧ minWinners ≤ saleCount values (values i) then
    values i
  else
    0

/--
A threshold price rule is own-bid independent when changing bidder `i`'s report
does not change the price offered to `i`.
-/
def OwnBidIndependent [DecidableEq Agent]
    (threshold : (Agent → ℝ) → Agent → ℝ) : Prop :=
  ∀ (bids : Agent → ℝ) (i : Agent) (report : ℝ),
    threshold (Function.update bids i report) i = threshold bids i

/-- Bid profile with bidder `i`'s own bid erased to `0`. -/
def eraseOwnBid [DecidableEq Agent]
    (bids : Agent → ℝ) (i : Agent) : Agent → ℝ :=
  Function.update bids i 0

/--
Build a threshold rule from a pricing rule that only sees bidder `i`'s own bid
after it has been erased. This is the direct formal hook for random-sampling
and market-price auctions whose offer to `i` is computed from other bidders.
-/
def ownErasedThreshold [DecidableEq Agent]
    (priceRule : Agent → (Agent → ℝ) → ℝ) :
    (Agent → ℝ) → Agent → ℝ :=
  fun bids i => priceRule i (eraseOwnBid bids i)

/-- Keep bids on one side of a sample partition and zero the rest. -/
def restrictBidsBySide (side : Agent → Bool) (keep : Bool)
    (bids : Agent → ℝ) : Agent → ℝ :=
  fun j => if side j = keep then bids j else 0

/-- Total bid value `T` used by the weighted-pairing auction. -/
noncomputable def totalBidValue [Fintype Agent] (values : Agent → ℝ) : ℝ :=
  ∑ i : Agent, values i

/--
Expected payment of bidder `i` in the weighted-pairing auction. Bidder `i`
draws another bidder `j` with probability proportional to `values j`; if
`values j <= values i`, bidder `i` wins and pays `values j`.
-/
noncomputable def weightedPairingExpectedPayment
    [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (i : Agent) : ℝ :=
  ∑ j : Agent,
    if j ≠ i ∧ values j ≤ values i then
      (values j) ^ 2 / (totalBidValue values - values i)
    else
      0

/-- Expected revenue of the weighted-pairing auction. -/
noncomputable def weightedPairingExpectedRevenue
    [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) : ℝ :=
  ∑ i : Agent, weightedPairingExpectedPayment values i

/--
Cross-sample threshold rule using the nonnegative finite candidate offer price.
This is the deterministic core of the RSOP auction for a fixed partition.
-/
noncomputable def crossSampleCandidateOfferThreshold
    [Fintype Agent] [Nonempty Agent]
    (side : Agent → Bool) (minWinners : ℕ) :
    (Agent → ℝ) → Agent → ℝ :=
  fun bids i =>
    finiteCandidateOfferPrice
      (restrictBidsBySide side (!side i) bids) minWinners

/--
Digital-goods auction that offers every bidder a threshold price and sells iff
the bid meets that threshold.
-/
noncomputable def thresholdPriceAuction [DecidableEq Agent]
    (threshold : (Agent → ℝ) → Agent → ℝ) : DigitalGoodsAuction Agent where
  allocation bids i := if threshold bids i ≤ bids i then 1 else 0
  payment bids i := if threshold bids i ≤ bids i then threshold bids i else 0

/-- The finite `F^(2)` fixed-price benchmark value. -/
noncomputable def twoWinnerFixedPriceBenchmarkValue
    [Fintype Agent] [Nonempty Agent] (values : Agent → ℝ) : ℝ :=
  finiteCandidateFixedPriceBenchmark values 2

/--
Revenue of an arbitrary deterministic bid-independent threshold price rule on
a two-value input with high value `H` and low value `1`.

The price offered to a high bidder sees one fewer high bidder; the price offered
to a low bidder sees one fewer low bidder. A bidder pays the threshold exactly
when her value meets it.
-/
noncomputable def twoValueBidIndependentPriceRevenue
    (price : ℕ → ℕ → ℝ) (H highCount lowCount : ℕ) : ℝ :=
  (highCount : ℝ) *
      (if price (highCount - 1) lowCount ≤ (H : ℝ) then
        price (highCount - 1) lowCount else 0) +
    (lowCount : ℝ) *
      (if price highCount (lowCount - 1) ≤ 1 then
        price highCount (lowCount - 1) else 0)

/-- Concrete bidder type for a binary-valued input with `highCount` high bids
and `lowCount` low bids. -/
abbrev TwoValueAgent (highCount lowCount : ℕ) :=
  Fin highCount ⊕ Fin lowCount

/-- Binary-valued bid profile with high value `H` and low value `1`. -/
def twoValueBidProfile (H highCount lowCount : ℕ) :
    TwoValueAgent highCount lowCount → ℝ
  | Sum.inl _ => (H : ℝ)
  | Sum.inr _ => 1

/--
The one-winner finite fixed-price benchmark on a binary two-value input. The
empty-profile fallback is zero; all Section 9 witnesses below are nonempty.
-/
noncomputable def twoValueFixedPriceBenchmark
    (H highCount lowCount : ℕ) : ℝ :=
  if hzero : highCount + lowCount = 0 then 0 else
    @finiteCandidateFixedPriceBenchmark
      (TwoValueAgent highCount lowCount) inferInstance
      (sorry)
      (twoValueBidProfile H highCount lowCount) 1

/--
Canonical erased-bid list for a binary input: `highCount` copies of the high
value followed by `lowCount` copies of the low value `1`.
-/
def twoValueErasedBidList (H highCount lowCount : ℕ) : List ℝ :=
  List.replicate highCount (H : ℝ) ++ List.replicate lowCount 1

/--
Restrict a paper-style anonymous bid-independent price rule on erased bid
lists to binary inputs. On binary inputs the canonical list is determined by
the high/low counts, which is the count-threshold model used in the deterministic-threshold lower-bound theorem.
-/
def twoValueListBidIndependentThresholdPrice
    (priceRule : List ℝ → ℝ) (H : ℕ) : ℕ → ℕ → ℝ :=
  fun highCount lowCount =>
    priceRule (twoValueErasedBidList H highCount lowCount)

/--
Utility from reporting `report` in a deterministic single-parameter offer
slice. `none` means rejection; `some p` means winning and paying `p`.
-/
def deterministicOfferUtility (offer : ℝ → Option ℝ)
    (value report : ℝ) : ℝ :=
  match offer report with
  | some price => value - price
  | none => 0

/-- Dominant-strategy truthfulness for a fixed-other-bids deterministic offer. -/
def DeterministicOfferTruthful (offer : ℝ → Option ℝ) : Prop :=
  ∀ value report,
    deterministicOfferUtility offer value report ≤
      deterministicOfferUtility offer value value

/-- A winning bidder is never charged above her own report. -/
def DeterministicOfferFeasible (offer : ℝ → Option ℝ) : Prop :=
  ∀ report price, offer report = some price → price ≤ report

/--
A deterministic offer slice is dominated by a threshold if every winning report
pays exactly that threshold and the threshold is no larger than the winning
report.
-/
def DeterministicOfferThresholdDominates
    (offer : ℝ → Option ℝ) (threshold : ℝ) : Prop :=
  ∀ report price,
    offer report = some price → price = threshold ∧ threshold ≤ report

namespace DigitalGoodsAuction

/-- A deterministic digital-goods auction has binary allocation outcomes. -/
def BinaryAllocation (M : DigitalGoodsAuction Agent) : Prop :=
  ∀ bids i, M.allocation bids i = 0 ∨ M.allocation bids i = 1

end DigitalGoodsAuction

/--
The single-bidder deterministic offer slice induced by a full digital-goods
auction after fixing the other bids.
-/
noncomputable def deterministicAuctionOffer [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent) (bids : Agent → ℝ) (i : Agent) :
    ℝ → Option ℝ :=
  fun report =>
    let profile := Function.update bids i report
    if M.allocation profile i = 1 then
      some (M.payment profile i)
    else
      none

end Auction

end EconCSLib
