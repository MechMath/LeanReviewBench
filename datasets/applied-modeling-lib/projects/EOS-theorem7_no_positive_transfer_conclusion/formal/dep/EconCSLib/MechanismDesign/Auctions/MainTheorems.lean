import Mathlib
import dep.EconCSLib.MechanismDesign.Auctions.Position

open MeasureTheory

open ProbabilityTheory

namespace EconCSLib

namespace Auction

def paper_position_no_positive_transfers
    {Bidder Slot : Type*} (O : PositionOutcome Bidder Slot) : Prop :=
  ∀ i, 0 ≤ O.paymentPerClick i

noncomputable def paper_theorem7_bstar_bid
    (value vcgTotalPayment clickThroughRate : ℕ → ℝ) (rank : ℕ) : ℝ :=
  match rank with
  | 0 => value 0
  | i + 1 => vcgTotalPayment i / clickThroughRate i

def paper_theorem7_ranked_environment
    {n : ℕ} (clickThroughRate : ℕ → ℝ) : PositionEnvironment (Fin n) where
  clickThroughRate i := clickThroughRate i.val

noncomputable def paper_theorem7_ranked_bstar_outcome
    {n : ℕ} (value vcgTotalPayment clickThroughRate : ℕ → ℝ) :
    PositionOutcome (Fin n) (Fin n) where
  slotOf i := some i
  paymentPerClick i :=
    paper_theorem7_bstar_bid
      value vcgTotalPayment clickThroughRate (i.val + 1)

def paper_theorem7_ranked_vcg_tail_payment
    (value clickThroughRate : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _i, 0 => 0
  | i, remaining + 1 =>
      (clickThroughRate i - clickThroughRate (i + 1)) * value (i + 1) +
        paper_theorem7_ranked_vcg_tail_payment
          value clickThroughRate (i + 1) remaining

def paper_theorem7_ranked_canonical_tail_remaining
    {n : ℕ} (i : Fin n) : ℕ :=
  n - (i.val + 1)

structure PaperTheorem7OrderedRankedCanonicalTailComparisonPaymentCertificate
    (n : ℕ) where
  value : ℕ → ℝ
  vcgTotalPayment : ℕ → ℝ
  clickThroughRate : ℕ → ℝ
  vcgOutcome : PositionOutcome (Fin n) (Fin n)
  click_nonneg : ∀ s : Fin n, 0 ≤ clickThroughRate s.val
  click_pos : ∀ s : Fin n, 0 < clickThroughRate s.val
  click_mono : ∀ k : ℕ, clickThroughRate (k + 1) ≤ clickThroughRate k
  value_mono : ∀ a b : ℕ, a ≤ b → value b ≤ value a
  vcg_rec :
    ∀ k : ℕ,
      vcgTotalPayment k =
        (clickThroughRate k - clickThroughRate (k + 1)) * value (k + 1) +
          vcgTotalPayment (k + 1)
  payment_le_value :
    ∀ i : Fin n,
      vcgTotalPayment i.val ≤ clickThroughRate i.val * value i.val
  vcg_tail_eq :
    ∀ i : Fin n,
      vcgTotalPayment i.val =
        paper_theorem7_ranked_vcg_tail_payment
          value clickThroughRate i.val
          (paper_theorem7_ranked_canonical_tail_remaining i)
  same_slots_as_vcg :
    ∀ i,
      (paper_theorem7_ranked_bstar_outcome
        value vcgTotalPayment clickThroughRate).slotOf i =
        vcgOutcome.slotOf i
  same_payments_as_vcg :
    ∀ i,
      (paper_theorem7_ranked_bstar_outcome
        value vcgTotalPayment clickThroughRate).paymentPerClick i =
        vcgOutcome.paymentPerClick i

structure PaperTheorem8GeneralizedEnglishAuctionState (Bidder : Type*) where
  clockPrice : ℝ
  lastDropout : Bidder → Option ℝ

namespace PaperTheorem8GeneralizedEnglishAuctionState

end PaperTheorem8GeneralizedEnglishAuctionState

namespace PaperTheorem8GeneralizedEnglishDynamicGame

end PaperTheorem8GeneralizedEnglishDynamicGame

end Auction

end EconCSLib
