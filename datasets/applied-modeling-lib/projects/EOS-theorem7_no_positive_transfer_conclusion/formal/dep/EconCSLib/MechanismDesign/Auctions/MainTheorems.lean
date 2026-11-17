import Mathlib
import dep.EconCSLib.MechanismDesign.Auctions.Position

open MeasureTheory
open ProbabilityTheory

/-!
# Paper-Facing Theorems: Auction Test-of-Time Tracks

This file is the public theorem interface for the current auction-theory
formalization work around SIGecom Test-of-Time papers:

- the 2021 digital-goods/prior-free-auction paper,
- the 2018 GSP/position-auction paper series,
- the 2017 combinatorial-auction paper.

The full approximation/equilibrium theorems remain future work; this file
exposes the closed unconditional theorem surface now available.
-/

namespace EconCSLib
namespace Auction

/-! ## 1) Paper-Facing Definitions: 2021 Digital Goods -/

/- Paper Definition: The revenue of a digital goods auction outcome.
    $\sum_{i \in \text{winners}} p_i$
-/
theorem paper_position_slot_envy_free_stable_assignment
    {Bidder Slot : Type*}
    (E : PositionEnvironment Slot)
    (O : PositionOutcome Bidder Slot) (values : Bidder → ℝ)
    (hfeasible : O.FeasibleAssignment)
    (hIR : O.IndividuallyRational E values)
    (h : O.SlotEnvyFree E values) :
    O.StableAssignment E values := by
  exact PositionOutcome.stableAssignment_of_slotEnvyFree
    E O values hfeasible hIR h

/-
EOS Lemma 5 static-game form. The outcome of a feasible, individually rational
locally envy-free equilibrium of the GSP-induced static game is a stable
assignment.
-/
theorem paper_position_stable_assignment_payment_lower_bound_pair
    {n : ℕ}
    (E : PositionEnvironment (Fin n))
    (O : PositionOutcome (Fin n) (Fin n)) (values : Fin n → ℝ)
    (hstable : O.StableAssignment E values)
    (i j : Fin n)
    (hslot_i : O.slotOf i = some i)
    (hslot_j : O.slotOf j = some j) :
    (E.clickThroughRate i - E.clickThroughRate j) * values j +
        E.clickThroughRate j * O.paymentPerClick j ≤
      E.clickThroughRate i * O.paymentPerClick i := by
  have hno := hstable.2.2 j i i hslot_i
  have hutil :
      O.utility E values j =
        E.clickThroughRate j * (values j - O.paymentPerClick j) := by
    simp [PositionOutcome.utility, hslot_j]
  rw [hutil] at hno
  nlinarith

/-
EOS Theorem 7 revenue-comparison algebra. If the VCG-equivalent outcome and
another locally envy-free outcome assign the same slots, and the
VCG-equivalent outcome has weakly lower per-click payments bidder-by-bidder,
then the seller revenue in the other outcome is weakly higher.
-/
theorem paper_position_revenue_le_of_same_slots_payment_le
    {Bidder Slot : Type*} [Fintype Bidder]
    (E : PositionEnvironment Slot)
    (vcgLike other : PositionOutcome Bidder Slot)
    (hctr : ∀ s, 0 ≤ E.clickThroughRate s)
    (hsame_slot : ∀ i, vcgLike.slotOf i = other.slotOf i)
    (hpay_le : ∀ i, vcgLike.paymentPerClick i ≤ other.paymentPerClick i) :
    vcgLike.revenue E ≤ other.revenue E := by
  exact PositionOutcome.revenue_le_of_same_slots_payment_le
    E vcgLike other hctr hsame_slot hpay_le

/-
Paper-facing no-positive-transfers/no-subsidy condition for position-auction
outcomes: every bidder's per-click payment is nonnegative.
-/
def paper_position_no_positive_transfers
    {Bidder Slot : Type*} (O : PositionOutcome Bidder Slot) : Prop :=
  ∀ i, 0 ≤ O.paymentPerClick i

/- The paper-facing no-positive-transfers condition is exactly payment
nonnegativity for each bidder. -/
noncomputable def paper_theorem7_bstar_bid
    (value vcgTotalPayment clickThroughRate : ℕ → ℝ) (rank : ℕ) : ℝ :=
  match rank with
  | 0 => value 0
  | i + 1 => vcgTotalPayment i / clickThroughRate i

/-
EOS Theorem 7 payment identity. In GSP, if rank `i` pays the next rank's
`B*` bid per click, then rank `i`'s total payment is exactly the VCG total
payment `p^{V,(i)}`.
-/
theorem paper_theorem7_bstar_next_bid_payment_eq_vcg
    (value vcgTotalPayment clickThroughRate : ℕ → ℝ) (i : ℕ)
    (hclick_ne : clickThroughRate i ≠ 0) :
    clickThroughRate i *
      paper_theorem7_bstar_bid value vcgTotalPayment clickThroughRate (i + 1) =
      vcgTotalPayment i := by
  simp [paper_theorem7_bstar_bid]
  field_simp [hclick_ne]

/-
EOS Theorem 7 `B*` bid nonnegativity. If values, VCG total payments, and
click-through denominators have the standard signs, every `B*` bid is
nonnegative.
-/
def paper_theorem7_ranked_environment
    {n : ℕ} (clickThroughRate : ℕ → ℝ) : PositionEnvironment (Fin n) where
  clickThroughRate i := clickThroughRate i.val

/-
EOS Theorem 7 finite ranked `B*` GSP outcome. Bidder/rank `i` receives slot
`i` and pays the next `B*` bid per click.
-/
noncomputable def paper_theorem7_ranked_bstar_outcome
    {n : ℕ} (value vcgTotalPayment clickThroughRate : ℕ → ℝ) :
    PositionOutcome (Fin n) (Fin n) where
  slotOf i := some i
  paymentPerClick i :=
    paper_theorem7_bstar_bid
      value vcgTotalPayment clickThroughRate (i.val + 1)

/- EOS Theorem 7 ranked `B*` outcome slot projection. -/
theorem paper_theorem7_ranked_bstar_outcome_feasible
    {n : ℕ} (value vcgTotalPayment clickThroughRate : ℕ → ℝ) :
    (paper_theorem7_ranked_bstar_outcome
      value vcgTotalPayment clickThroughRate :
        PositionOutcome (Fin n) (Fin n)).FeasibleAssignment := by
  intro i j s hi hj
  simp [paper_theorem7_ranked_bstar_outcome] at hi hj
  exact hi.trans hj.symm

/-
EOS Theorem 7 ranked `B*` total-payment identity. In the finite ranked outcome,
rank `i`'s click-through rate times its per-click payment is exactly the
specified VCG total payment.
-/
theorem paper_theorem7_ranked_bstar_outcome_total_payment_eq_vcg
    {n : ℕ} (value vcgTotalPayment clickThroughRate : ℕ → ℝ) (i : Fin n)
    (hclick_ne : clickThroughRate i.val ≠ 0) :
    (paper_theorem7_ranked_environment clickThroughRate).clickThroughRate i *
      (paper_theorem7_ranked_bstar_outcome
        value vcgTotalPayment clickThroughRate).paymentPerClick i =
      vcgTotalPayment i.val := by
  exact
    paper_theorem7_bstar_next_bid_payment_eq_vcg
      value vcgTotalPayment clickThroughRate i.val hclick_ne

/-
EOS Theorem 7 ranked `B*` individual rationality criterion. If each ranked VCG
total payment is at most the bidder's click-weighted value, then the finite
ranked `B*` outcome is individually rational.
-/
theorem paper_theorem7_ranked_bstar_outcome_individually_rational
    {n : ℕ} (value vcgTotalPayment clickThroughRate : ℕ → ℝ)
    (hclick_ne : ∀ i : Fin n, clickThroughRate i.val ≠ 0)
    (hpayment_le_value :
      ∀ i : Fin n,
        vcgTotalPayment i.val ≤ clickThroughRate i.val * value i.val) :
    (paper_theorem7_ranked_bstar_outcome
      value vcgTotalPayment clickThroughRate).IndividuallyRational
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun i : Fin n => value i.val) := by
  intro i
  have htotal_eq :
      (paper_theorem7_ranked_environment clickThroughRate).clickThroughRate i *
        (paper_theorem7_ranked_bstar_outcome
          value vcgTotalPayment clickThroughRate).paymentPerClick i =
        vcgTotalPayment i.val :=
    paper_theorem7_ranked_bstar_outcome_total_payment_eq_vcg
      value vcgTotalPayment clickThroughRate i (hclick_ne i)
  have hmul_le :
      clickThroughRate i.val *
          (paper_theorem7_ranked_bstar_outcome
            value vcgTotalPayment clickThroughRate).paymentPerClick i ≤
        clickThroughRate i.val * value i.val := by
    simpa [paper_theorem7_ranked_environment] using
      htotal_eq.symm ▸ hpayment_le_value i
  have hnonneg :
      0 ≤
        clickThroughRate i.val * value i.val -
          clickThroughRate i.val *
            (paper_theorem7_ranked_bstar_outcome
              value vcgTotalPayment clickThroughRate).paymentPerClick i :=
    sub_nonneg.mpr hmul_le
  simpa [PositionOutcome.utility, paper_theorem7_ranked_environment,
    paper_theorem7_ranked_bstar_outcome, mul_sub] using hnonneg

/-
EOS Theorem 7 ranked `B*` slot-envy bridge. To prove the formal
`SlotEnvyFree` predicate for the finite ranked outcome, it suffices to prove
the concrete pairwise ranked envy inequalities.
-/
theorem paper_theorem7_ranked_bstar_outcome_slot_envy_free_of_pairwise
    {n : ℕ} (value vcgTotalPayment clickThroughRate : ℕ → ℝ)
    (hpairwise :
      ∀ i j : Fin n,
        clickThroughRate j.val *
            (value i.val -
              (paper_theorem7_ranked_bstar_outcome
                value vcgTotalPayment clickThroughRate).paymentPerClick j) ≤
          clickThroughRate i.val *
            (value i.val -
              (paper_theorem7_ranked_bstar_outcome
                value vcgTotalPayment clickThroughRate).paymentPerClick i)) :
    (paper_theorem7_ranked_bstar_outcome
      value vcgTotalPayment clickThroughRate).SlotEnvyFree
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun i : Fin n => value i.val) := by
  intro i j s hslot
  have hs : j = s := by
    simpa [paper_theorem7_ranked_bstar_outcome] using hslot
  subst s
  simpa [PositionOutcome.utility, paper_theorem7_ranked_environment,
    paper_theorem7_ranked_bstar_outcome] using hpairwise i j

/-
EOS Theorem 7 exact ranked slot-envy characterization. For the finite ranked
`B*` outcome, the abstract `SlotEnvyFree` predicate is equivalent to the
concrete pairwise ranked envy inequalities.
-/
theorem paper_theorem7_ranked_vcg_adjacent_no_envy_higher_of_value_le
    {value totalPayment clickThroughRate : ℕ → ℝ} {bidder rank : ℕ}
    (hclick_mono : clickThroughRate (rank + 1) ≤ clickThroughRate rank)
    (hvalue_le : value bidder ≤ value (rank + 1))
    (hrec :
      totalPayment rank =
        (clickThroughRate rank - clickThroughRate (rank + 1)) *
            value (rank + 1) +
          totalPayment (rank + 1)) :
    clickThroughRate rank * value bidder - totalPayment rank ≤
      clickThroughRate (rank + 1) * value bidder -
        totalPayment (rank + 1) := by
  have hdiff_nonneg :
      0 ≤ clickThroughRate rank - clickThroughRate (rank + 1) :=
    sub_nonneg.mpr hclick_mono
  have hmul :
      (clickThroughRate rank - clickThroughRate (rank + 1)) *
          value bidder ≤
        (clickThroughRate rank - clickThroughRate (rank + 1)) *
          value (rank + 1) :=
    mul_le_mul_of_nonneg_left hvalue_le hdiff_nonneg
  rw [hrec]
  nlinarith

/-
EOS Theorem 7 adjacent no-envy algebra for higher-valued bidders. Under the VCG
payment recursion, if bidder `bidder` has value at least the next rank's value,
then bidder `bidder` weakly prefers the higher adjacent slot/payment to the
lower adjacent slot/payment.
-/
theorem paper_theorem7_ranked_vcg_adjacent_no_envy_lower_of_value_ge
    {value totalPayment clickThroughRate : ℕ → ℝ} {bidder rank : ℕ}
    (hclick_mono : clickThroughRate (rank + 1) ≤ clickThroughRate rank)
    (hvalue_ge : value (rank + 1) ≤ value bidder)
    (hrec :
      totalPayment rank =
        (clickThroughRate rank - clickThroughRate (rank + 1)) *
            value (rank + 1) +
          totalPayment (rank + 1)) :
    clickThroughRate (rank + 1) * value bidder -
        totalPayment (rank + 1) ≤
      clickThroughRate rank * value bidder - totalPayment rank := by
  have hdiff_nonneg :
      0 ≤ clickThroughRate rank - clickThroughRate (rank + 1) :=
    sub_nonneg.mpr hclick_mono
  have hmul :
      (clickThroughRate rank - clickThroughRate (rank + 1)) *
          value (rank + 1) ≤
        (clickThroughRate rank - clickThroughRate (rank + 1)) *
          value bidder :=
    mul_le_mul_of_nonneg_left hvalue_ge hdiff_nonneg
  rw [hrec]
  nlinarith

/-
EOS Theorem 7 telescoping helper. If a ranked utility quantity is weakly
increasing at each adjacent step from `start` through `start + steps`, then the
endpoint comparison holds.
-/
theorem paper_theorem7_ranked_chain_le_of_adjacent
    (utility : ℕ → ℝ) (start steps : ℕ)
    (hadj :
      ∀ k : ℕ,
        start ≤ k →
          k < start + steps →
            utility k ≤ utility (k + 1)) :
    utility start ≤ utility (start + steps) := by
  induction steps generalizing start with
  | zero =>
      simp
  | succ steps ih =>
      have hfirst : utility start ≤ utility (start + 1) :=
        hadj start le_rfl
          (Nat.lt_add_of_pos_right (Nat.succ_pos steps))
      have hrest : utility (start + 1) ≤ utility ((start + 1) + steps) := by
        exact
          ih (start + 1) (by
            intro k hkge hklt
            exact
              hadj k (Nat.le_trans (Nat.le_succ start) hkge) (by
                simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using hklt))
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using le_trans hfirst hrest

/-
EOS Theorem 7 reverse telescoping helper. If a ranked utility quantity is
weakly decreasing at each adjacent step from `start` through `start + steps`,
then the endpoint comparison holds in the reverse direction.
-/
theorem paper_theorem7_ranked_chain_ge_of_adjacent
    (utility : ℕ → ℝ) (start steps : ℕ)
    (hadj :
      ∀ k : ℕ,
        start ≤ k →
          k < start + steps →
            utility (k + 1) ≤ utility k) :
    utility (start + steps) ≤ utility start := by
  induction steps generalizing start with
  | zero =>
      simp
  | succ steps ih =>
      have hfirst : utility (start + 1) ≤ utility start :=
        hadj start le_rfl
          (Nat.lt_add_of_pos_right (Nat.succ_pos steps))
      have hrest : utility ((start + 1) + steps) ≤ utility (start + 1) := by
        exact
          ih (start + 1) (by
            intro k hkge hklt
            exact
              hadj k (Nat.le_trans (Nat.le_succ start) hkge) (by
                simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using hklt))
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using le_trans hrest hfirst

/-
EOS Theorem 7 telescoped no-envy algebra for lower-valued bidders. Combining
the adjacent VCG no-envy steps shows that a bidder whose value is weakly below
each intervening next-rank value weakly prefers the lower endpoint to the
higher endpoint.
-/
theorem paper_theorem7_ranked_vcg_no_envy_higher_chain_of_value_le
    {value totalPayment clickThroughRate : ℕ → ℝ} {bidder start steps : ℕ}
    (hclick_mono :
      ∀ k : ℕ,
        start ≤ k →
          k < start + steps →
            clickThroughRate (k + 1) ≤ clickThroughRate k)
    (hvalue_le :
      ∀ k : ℕ,
        start ≤ k →
          k < start + steps →
            value bidder ≤ value (k + 1))
    (hrec :
      ∀ k : ℕ,
        start ≤ k →
          k < start + steps →
            totalPayment k =
              (clickThroughRate k - clickThroughRate (k + 1)) *
                  value (k + 1) +
                totalPayment (k + 1)) :
    clickThroughRate start * value bidder - totalPayment start ≤
      clickThroughRate (start + steps) * value bidder -
        totalPayment (start + steps) := by
  exact
    paper_theorem7_ranked_chain_le_of_adjacent
      (fun k => clickThroughRate k * value bidder - totalPayment k)
      start steps
      (by
        intro k hkge hklt
        exact
          paper_theorem7_ranked_vcg_adjacent_no_envy_higher_of_value_le
            (hclick_mono k hkge hklt)
            (hvalue_le k hkge hklt)
            (hrec k hkge hklt))

/-
EOS Theorem 7 telescoped no-envy algebra for higher-valued bidders. Combining
the adjacent VCG no-envy steps shows that a bidder whose value is weakly above
each intervening next-rank value weakly prefers the higher endpoint to the
lower endpoint.
-/
theorem paper_theorem7_ranked_vcg_no_envy_lower_chain_of_value_ge
    {value totalPayment clickThroughRate : ℕ → ℝ} {bidder start steps : ℕ}
    (hclick_mono :
      ∀ k : ℕ,
        start ≤ k →
          k < start + steps →
            clickThroughRate (k + 1) ≤ clickThroughRate k)
    (hvalue_ge :
      ∀ k : ℕ,
        start ≤ k →
          k < start + steps →
            value (k + 1) ≤ value bidder)
    (hrec :
      ∀ k : ℕ,
        start ≤ k →
          k < start + steps →
            totalPayment k =
              (clickThroughRate k - clickThroughRate (k + 1)) *
                  value (k + 1) +
                totalPayment (k + 1)) :
    clickThroughRate (start + steps) * value bidder -
        totalPayment (start + steps) ≤
      clickThroughRate start * value bidder - totalPayment start := by
  exact
    paper_theorem7_ranked_chain_ge_of_adjacent
      (fun k => clickThroughRate k * value bidder - totalPayment k)
      start steps
      (by
        intro k hkge hklt
        exact
          paper_theorem7_ranked_vcg_adjacent_no_envy_lower_of_value_ge
            (hclick_mono k hkge hklt)
            (hvalue_ge k hkge hklt)
            (hrec k hkge hklt))

/-
EOS Theorem 7 endpoint no-envy algebra for a lower-ranked bidder. Under the
standard value ordering along the interval, rank `start + steps` weakly prefers
its own lower endpoint slot/payment to rank `start`'s higher endpoint
slot/payment.
-/
theorem paper_theorem7_ranked_vcg_lower_rank_no_envy_higher_endpoint
    {value totalPayment clickThroughRate : ℕ → ℝ} {start steps : ℕ}
    (hclick_mono :
      ∀ k : ℕ,
        start ≤ k →
          k < start + steps →
            clickThroughRate (k + 1) ≤ clickThroughRate k)
    (hvalue_order :
      ∀ k : ℕ,
        start ≤ k →
          k < start + steps →
            value (start + steps) ≤ value (k + 1))
    (hrec :
      ∀ k : ℕ,
        start ≤ k →
          k < start + steps →
            totalPayment k =
              (clickThroughRate k - clickThroughRate (k + 1)) *
                  value (k + 1) +
                totalPayment (k + 1)) :
    clickThroughRate start * value (start + steps) - totalPayment start ≤
      clickThroughRate (start + steps) * value (start + steps) -
        totalPayment (start + steps) := by
  exact
    paper_theorem7_ranked_vcg_no_envy_higher_chain_of_value_le
      hclick_mono hvalue_order hrec

/-
EOS Theorem 7 endpoint no-envy algebra for a higher-ranked bidder. Under the
standard value ordering along the interval, rank `start` weakly prefers its own
higher endpoint slot/payment to rank `start + steps`'s lower endpoint
slot/payment.
-/
theorem paper_theorem7_ranked_vcg_higher_rank_no_envy_lower_endpoint
    {value totalPayment clickThroughRate : ℕ → ℝ} {start steps : ℕ}
    (hclick_mono :
      ∀ k : ℕ,
        start ≤ k →
          k < start + steps →
            clickThroughRate (k + 1) ≤ clickThroughRate k)
    (hvalue_order :
      ∀ k : ℕ,
        start ≤ k →
          k < start + steps →
            value (k + 1) ≤ value start)
    (hrec :
      ∀ k : ℕ,
        start ≤ k →
          k < start + steps →
            totalPayment k =
              (clickThroughRate k - clickThroughRate (k + 1)) *
                  value (k + 1) +
                totalPayment (k + 1)) :
    clickThroughRate (start + steps) * value start -
        totalPayment (start + steps) ≤
      clickThroughRate start * value start - totalPayment start := by
  exact
    paper_theorem7_ranked_vcg_no_envy_lower_chain_of_value_ge
      hclick_mono hvalue_order hrec

/-
EOS Theorem 7 oriented finite-rank pairwise envy inequality. If rank `i` is
weakly below rank `j`, then the endpoint no-envy algebra and the `B*`
total-payment identity show that bidder `i` does not prefer rank `j`'s higher
slot/payment.
-/
theorem paper_theorem7_ranked_bstar_outcome_lower_fin_no_envy_higher
    {n : ℕ} {value vcgTotalPayment clickThroughRate : ℕ → ℝ}
    (i j : Fin n) (hji : j.val ≤ i.val)
    (hclick_ne : ∀ r : Fin n, clickThroughRate r.val ≠ 0)
    (hclick_mono :
      ∀ k : ℕ,
        j.val ≤ k →
          k < i.val →
            clickThroughRate (k + 1) ≤ clickThroughRate k)
    (hvalue_order :
      ∀ k : ℕ,
        j.val ≤ k →
          k < i.val →
            value i.val ≤ value (k + 1))
    (hrec :
      ∀ k : ℕ,
        j.val ≤ k →
          k < i.val →
            vcgTotalPayment k =
              (clickThroughRate k - clickThroughRate (k + 1)) *
                  value (k + 1) +
                vcgTotalPayment (k + 1)) :
    clickThroughRate j.val *
        (value i.val -
          (paper_theorem7_ranked_bstar_outcome
            value vcgTotalPayment clickThroughRate).paymentPerClick j) ≤
      clickThroughRate i.val *
        (value i.val -
          (paper_theorem7_ranked_bstar_outcome
            value vcgTotalPayment clickThroughRate).paymentPerClick i) := by
  have hendpoint :
      clickThroughRate j.val * value i.val - vcgTotalPayment j.val ≤
        clickThroughRate i.val * value i.val - vcgTotalPayment i.val := by
    have hraw :=
      paper_theorem7_ranked_vcg_lower_rank_no_envy_higher_endpoint
        (value := value) (totalPayment := vcgTotalPayment)
        (clickThroughRate := clickThroughRate) (start := j.val)
        (steps := i.val - j.val)
        (by
          intro k hkge hklt
          exact hclick_mono k hkge
            (by
              simpa [Nat.add_sub_of_le hji] using hklt))
        (by
          intro k hkge hklt
          simpa [Nat.add_sub_of_le hji] using
            hvalue_order k hkge
              (by
                simpa [Nat.add_sub_of_le hji] using hklt))
        (by
          intro k hkge hklt
          exact hrec k hkge
            (by
              simpa [Nat.add_sub_of_le hji] using hklt))
    simpa [Nat.add_sub_of_le hji] using hraw
  have hpj :
      clickThroughRate j.val *
          (paper_theorem7_ranked_bstar_outcome
            value vcgTotalPayment clickThroughRate).paymentPerClick j =
        vcgTotalPayment j.val := by
    simpa [paper_theorem7_ranked_environment] using
      paper_theorem7_ranked_bstar_outcome_total_payment_eq_vcg
        value vcgTotalPayment clickThroughRate j (hclick_ne j)
  have hpi :
      clickThroughRate i.val *
          (paper_theorem7_ranked_bstar_outcome
            value vcgTotalPayment clickThroughRate).paymentPerClick i =
        vcgTotalPayment i.val := by
    simpa [paper_theorem7_ranked_environment] using
      paper_theorem7_ranked_bstar_outcome_total_payment_eq_vcg
        value vcgTotalPayment clickThroughRate i (hclick_ne i)
  calc
    clickThroughRate j.val *
        (value i.val -
          (paper_theorem7_ranked_bstar_outcome
            value vcgTotalPayment clickThroughRate).paymentPerClick j)
        =
      clickThroughRate j.val * value i.val -
        clickThroughRate j.val *
          (paper_theorem7_ranked_bstar_outcome
            value vcgTotalPayment clickThroughRate).paymentPerClick j := by
        ring
    _ = clickThroughRate j.val * value i.val - vcgTotalPayment j.val := by
        rw [hpj]
    _ ≤ clickThroughRate i.val * value i.val - vcgTotalPayment i.val :=
        hendpoint
    _ = clickThroughRate i.val * value i.val -
        clickThroughRate i.val *
          (paper_theorem7_ranked_bstar_outcome
            value vcgTotalPayment clickThroughRate).paymentPerClick i := by
        rw [hpi]
    _ =
      clickThroughRate i.val *
        (value i.val -
          (paper_theorem7_ranked_bstar_outcome
            value vcgTotalPayment clickThroughRate).paymentPerClick i) := by
        ring

/-
EOS Theorem 7 oriented finite-rank pairwise envy inequality. If rank `i` is
weakly above rank `j`, then the endpoint no-envy algebra and the `B*`
total-payment identity show that bidder `i` does not prefer rank `j`'s lower
slot/payment.
-/
theorem paper_theorem7_ranked_bstar_outcome_higher_fin_no_envy_lower
    {n : ℕ} {value vcgTotalPayment clickThroughRate : ℕ → ℝ}
    (i j : Fin n) (hij : i.val ≤ j.val)
    (hclick_ne : ∀ r : Fin n, clickThroughRate r.val ≠ 0)
    (hclick_mono :
      ∀ k : ℕ,
        i.val ≤ k →
          k < j.val →
            clickThroughRate (k + 1) ≤ clickThroughRate k)
    (hvalue_order :
      ∀ k : ℕ,
        i.val ≤ k →
          k < j.val →
            value (k + 1) ≤ value i.val)
    (hrec :
      ∀ k : ℕ,
        i.val ≤ k →
          k < j.val →
            vcgTotalPayment k =
              (clickThroughRate k - clickThroughRate (k + 1)) *
                  value (k + 1) +
                vcgTotalPayment (k + 1)) :
    clickThroughRate j.val *
        (value i.val -
          (paper_theorem7_ranked_bstar_outcome
            value vcgTotalPayment clickThroughRate).paymentPerClick j) ≤
      clickThroughRate i.val *
        (value i.val -
          (paper_theorem7_ranked_bstar_outcome
            value vcgTotalPayment clickThroughRate).paymentPerClick i) := by
  have hendpoint :
      clickThroughRate j.val * value i.val - vcgTotalPayment j.val ≤
        clickThroughRate i.val * value i.val - vcgTotalPayment i.val := by
    have hraw :=
      paper_theorem7_ranked_vcg_higher_rank_no_envy_lower_endpoint
        (value := value) (totalPayment := vcgTotalPayment)
        (clickThroughRate := clickThroughRate) (start := i.val)
        (steps := j.val - i.val)
        (by
          intro k hkge hklt
          exact hclick_mono k hkge
            (by
              simpa [Nat.add_sub_of_le hij] using hklt))
        (by
          intro k hkge hklt
          exact hvalue_order k hkge
            (by
              simpa [Nat.add_sub_of_le hij] using hklt))
        (by
          intro k hkge hklt
          exact hrec k hkge
            (by
              simpa [Nat.add_sub_of_le hij] using hklt))
    simpa [Nat.add_sub_of_le hij] using hraw
  have hpj :
      clickThroughRate j.val *
          (paper_theorem7_ranked_bstar_outcome
            value vcgTotalPayment clickThroughRate).paymentPerClick j =
        vcgTotalPayment j.val := by
    simpa [paper_theorem7_ranked_environment] using
      paper_theorem7_ranked_bstar_outcome_total_payment_eq_vcg
        value vcgTotalPayment clickThroughRate j (hclick_ne j)
  have hpi :
      clickThroughRate i.val *
          (paper_theorem7_ranked_bstar_outcome
            value vcgTotalPayment clickThroughRate).paymentPerClick i =
        vcgTotalPayment i.val := by
    simpa [paper_theorem7_ranked_environment] using
      paper_theorem7_ranked_bstar_outcome_total_payment_eq_vcg
        value vcgTotalPayment clickThroughRate i (hclick_ne i)
  calc
    clickThroughRate j.val *
        (value i.val -
          (paper_theorem7_ranked_bstar_outcome
            value vcgTotalPayment clickThroughRate).paymentPerClick j)
        =
      clickThroughRate j.val * value i.val -
        clickThroughRate j.val *
          (paper_theorem7_ranked_bstar_outcome
            value vcgTotalPayment clickThroughRate).paymentPerClick j := by
        ring
    _ = clickThroughRate j.val * value i.val - vcgTotalPayment j.val := by
        rw [hpj]
    _ ≤ clickThroughRate i.val * value i.val - vcgTotalPayment i.val :=
        hendpoint
    _ = clickThroughRate i.val * value i.val -
        clickThroughRate i.val *
          (paper_theorem7_ranked_bstar_outcome
            value vcgTotalPayment clickThroughRate).paymentPerClick i := by
        rw [hpi]
    _ =
      clickThroughRate i.val *
        (value i.val -
          (paper_theorem7_ranked_bstar_outcome
            value vcgTotalPayment clickThroughRate).paymentPerClick i) := by
        ring

/-
EOS Theorem 7 full finite ranked pairwise envy algebra. Under globally
decreasing click-through rates and ranked values, plus the VCG total-payment
recursion, every bidder weakly prefers its own ranked `B*` outcome slot/payment
to every other ranked slot/payment.
-/
theorem paper_theorem7_ranked_bstar_outcome_pairwise_envy_of_ordered_values
    {n : ℕ} {value vcgTotalPayment clickThroughRate : ℕ → ℝ}
    (hclick_ne : ∀ r : Fin n, clickThroughRate r.val ≠ 0)
    (hclick_mono : ∀ k : ℕ, clickThroughRate (k + 1) ≤ clickThroughRate k)
    (hvalue_mono : ∀ a b : ℕ, a ≤ b → value b ≤ value a)
    (hrec :
      ∀ k : ℕ,
        vcgTotalPayment k =
          (clickThroughRate k - clickThroughRate (k + 1)) *
              value (k + 1) +
            vcgTotalPayment (k + 1)) :
    ∀ i j : Fin n,
      clickThroughRate j.val *
          (value i.val -
            (paper_theorem7_ranked_bstar_outcome
              value vcgTotalPayment clickThroughRate).paymentPerClick j) ≤
        clickThroughRate i.val *
          (value i.val -
            (paper_theorem7_ranked_bstar_outcome
              value vcgTotalPayment clickThroughRate).paymentPerClick i) := by
  intro i j
  by_cases hji : j.val ≤ i.val
  · exact
      paper_theorem7_ranked_bstar_outcome_lower_fin_no_envy_higher
        i j hji hclick_ne
        (by
          intro k _hkge _hklt
          exact hclick_mono k)
        (by
          intro k _hkge hklt
          exact hvalue_mono (k + 1) i.val (Nat.succ_le_of_lt hklt))
        (by
          intro k _hkge _hklt
          exact hrec k)
  · have hij : i.val ≤ j.val := le_of_lt (lt_of_not_ge hji)
    exact
      paper_theorem7_ranked_bstar_outcome_higher_fin_no_envy_lower
        i j hij hclick_ne
        (by
          intro k _hkge _hklt
          exact hclick_mono k)
        (by
          intro k hkge _hklt
          exact hvalue_mono i.val (k + 1)
            (Nat.le_trans hkge (Nat.le_succ k)))
        (by
          intro k _hkge _hklt
          exact hrec k)

/-
EOS Theorem 7 adjacent-to-global local-envy bridge. The VCG recursion gives the
paper's adjacent local-envy inequalities, and under ordered ranks those
adjacent comparisons telescope to the full pairwise no-envy family used by the
formal `SlotEnvyFree` predicate.
-/
theorem paper_theorem7_ranked_bstar_outcome_slot_envy_free_of_ordered_values
    {n : ℕ} {value vcgTotalPayment clickThroughRate : ℕ → ℝ}
    (hclick_ne : ∀ r : Fin n, clickThroughRate r.val ≠ 0)
    (hclick_mono : ∀ k : ℕ, clickThroughRate (k + 1) ≤ clickThroughRate k)
    (hvalue_mono : ∀ a b : ℕ, a ≤ b → value b ≤ value a)
    (hrec :
      ∀ k : ℕ,
        vcgTotalPayment k =
          (clickThroughRate k - clickThroughRate (k + 1)) *
              value (k + 1) +
            vcgTotalPayment (k + 1)) :
    (paper_theorem7_ranked_bstar_outcome
      value vcgTotalPayment clickThroughRate).SlotEnvyFree
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun i : Fin n => value i.val) := by
  exact
    paper_theorem7_ranked_bstar_outcome_slot_envy_free_of_pairwise
      value vcgTotalPayment clickThroughRate
      (paper_theorem7_ranked_bstar_outcome_pairwise_envy_of_ordered_values
        hclick_ne hclick_mono hvalue_mono hrec)

/-
EOS Theorem 7 full finite ranked stable-assignment theorem. In addition to the
ordered-values VCG recursion assumptions, if each VCG total payment is below
the bidder's click-weighted value, the ranked `B*` outcome is a stable
assignment in the formal EOS predicate.
-/
theorem paper_theorem7_ranked_bstar_outcome_stable_assignment_of_ordered_values
    {n : ℕ} {value vcgTotalPayment clickThroughRate : ℕ → ℝ}
    (hclick_ne : ∀ r : Fin n, clickThroughRate r.val ≠ 0)
    (hclick_mono : ∀ k : ℕ, clickThroughRate (k + 1) ≤ clickThroughRate k)
    (hvalue_mono : ∀ a b : ℕ, a ≤ b → value b ≤ value a)
    (hrec :
      ∀ k : ℕ,
        vcgTotalPayment k =
          (clickThroughRate k - clickThroughRate (k + 1)) *
              value (k + 1) +
            vcgTotalPayment (k + 1))
    (hpayment_le_value :
      ∀ i : Fin n,
        vcgTotalPayment i.val ≤ clickThroughRate i.val * value i.val) :
    (paper_theorem7_ranked_bstar_outcome
      value vcgTotalPayment clickThroughRate).StableAssignment
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun i : Fin n => value i.val) := by
  exact
    paper_position_slot_envy_free_stable_assignment
      (paper_theorem7_ranked_environment clickThroughRate)
      (paper_theorem7_ranked_bstar_outcome
        value vcgTotalPayment clickThroughRate)
      (fun i : Fin n => value i.val)
      (paper_theorem7_ranked_bstar_outcome_feasible
        value vcgTotalPayment clickThroughRate)
      (paper_theorem7_ranked_bstar_outcome_individually_rational
        value vcgTotalPayment clickThroughRate hclick_ne hpayment_le_value)
      (paper_theorem7_ranked_bstar_outcome_slot_envy_free_of_ordered_values
        hclick_ne hclick_mono hvalue_mono hrec)

/-
Paper-facing ordered ranked certificate for EOS Theorem 7. This version removes
the raw pairwise-envy field from `PaperTheorem7RankedBStarCertificate`: Lean now
derives it from monotone click-through rates, monotone ranked values, and the
VCG total-payment recursion.
-/
def paper_theorem7_ranked_vcg_tail_payment
    (value clickThroughRate : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _i, 0 => 0
  | i, remaining + 1 =>
      (clickThroughRate i - clickThroughRate (i + 1)) * value (i + 1) +
        paper_theorem7_ranked_vcg_tail_payment
          value clickThroughRate (i + 1) remaining

/-
EOS Theorem 7 VCG tail-payment recursion. This is the source recursion used
to prove both payment equality for `B*` and adjacent local envy-freeness.
-/
theorem paper_theorem7_ranked_vcg_tail_payment_rec
    (value clickThroughRate : ℕ → ℝ) (i remaining : ℕ) :
    paper_theorem7_ranked_vcg_tail_payment
        value clickThroughRate i (remaining + 1) =
      (clickThroughRate i - clickThroughRate (i + 1)) * value (i + 1) +
        paper_theorem7_ranked_vcg_tail_payment
          value clickThroughRate (i + 1) remaining := by
  rfl

/-
EOS Theorem 7 nonnegativity of finite VCG tail payments. If click-through rates
are weakly decreasing by rank and values are nonnegative, every finite
tail-payment prefix is nonnegative.
-/
theorem paper_theorem7_ranked_vcg_tail_payment_nonneg
    {value clickThroughRate : ℕ → ℝ}
    (hvalue_nonneg : ∀ i, 0 ≤ value i)
    (hclick_mono : ∀ i, clickThroughRate (i + 1) ≤ clickThroughRate i)
    (i remaining : ℕ) :
    0 ≤
      paper_theorem7_ranked_vcg_tail_payment
        value clickThroughRate i remaining := by
  induction remaining generalizing i with
  | zero =>
      simp [paper_theorem7_ranked_vcg_tail_payment]
  | succ remaining ih =>
      rw [paper_theorem7_ranked_vcg_tail_payment_rec]
      exact
        add_nonneg
          (mul_nonneg
            (sub_nonneg.mpr (hclick_mono i))
            (hvalue_nonneg (i + 1)))
          (ih (i + 1))

/-
EOS Theorem 7 finite VCG-tail payment upper bound. Under nonnegative
click-through rates, nonnegative values, and values weakly decreasing by rank,
the finite VCG tail payment at rank `i` is bounded by the rank's click-weighted
value. This is the ranked individual-rationality payment bound for the
finite-tail VCG sequence.
-/
theorem paper_theorem7_ranked_vcg_tail_payment_le_of_adjacent_total_bounds
    (value clickThroughRate otherTotalPayment : ℕ → ℝ)
    (start remaining : ℕ)
    (hterminal : 0 ≤ otherTotalPayment (start + remaining))
    (hadj :
      ∀ k : ℕ,
        start ≤ k →
          k < start + remaining →
            (clickThroughRate k - clickThroughRate (k + 1)) *
                value (k + 1) +
              otherTotalPayment (k + 1) ≤ otherTotalPayment k) :
    paper_theorem7_ranked_vcg_tail_payment
        value clickThroughRate start remaining ≤
      otherTotalPayment start := by
  induction remaining generalizing start with
  | zero =>
      simpa [paper_theorem7_ranked_vcg_tail_payment] using hterminal
  | succ remaining ih =>
      rw [paper_theorem7_ranked_vcg_tail_payment_rec]
      have htail :
          paper_theorem7_ranked_vcg_tail_payment
              value clickThroughRate (start + 1) remaining ≤
            otherTotalPayment (start + 1) := by
        exact
          ih (start + 1)
            (by
              simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using hterminal)
            (by
              intro k hkge hklt
              exact
                hadj k
                  (Nat.le_trans (Nat.le_succ start) hkge)
                  (by
                    simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
                      Nat.add_left_comm] using hklt))
      have hfirst :
          (clickThroughRate start - clickThroughRate (start + 1)) *
              value (start + 1) +
            otherTotalPayment (start + 1) ≤ otherTotalPayment start :=
        hadj start le_rfl
          (Nat.lt_add_of_pos_right (Nat.succ_pos remaining))
      have htail_add :
          (clickThroughRate start - clickThroughRate (start + 1)) *
              value (start + 1) +
            paper_theorem7_ranked_vcg_tail_payment
              value clickThroughRate (start + 1) remaining ≤
          (clickThroughRate start - clickThroughRate (start + 1)) *
              value (start + 1) +
            otherTotalPayment (start + 1) :=
        by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left htail
              ((clickThroughRate start - clickThroughRate (start + 1)) *
                value (start + 1))
      exact le_trans htail_add hfirst

/-
EOS Theorem 7 ranked comparison-outcome total payment. If `rank < n`, this is
the click-through rate at that rank times the comparison outcome's per-click
payment at that rank; outside the finite range it is zero.
-/
def paper_theorem7_ranked_outcome_total_payment
    {n : ℕ} (clickThroughRate : ℕ → ℝ)
    (O : PositionOutcome (Fin n) (Fin n)) (rank : ℕ) : ℝ :=
  if h : rank < n then
    clickThroughRate rank * O.paymentPerClick ⟨rank, h⟩
  else
    0

/- EOS Theorem 7 projection for ranked comparison-outcome total payment. -/
theorem paper_theorem7_ranked_outcome_total_payment_of_fin
    {n : ℕ} (clickThroughRate : ℕ → ℝ)
    (O : PositionOutcome (Fin n) (Fin n)) (i : Fin n) :
    paper_theorem7_ranked_outcome_total_payment clickThroughRate O i.val =
      clickThroughRate i.val * O.paymentPerClick i := by
  simp [paper_theorem7_ranked_outcome_total_payment, i.isLt]

/-
EOS Theorem 7 comparison-outcome total payments are nonnegative at finite
ranks when click-through rates and per-click payments are nonnegative.
-/
theorem paper_theorem7_ranked_outcome_total_payment_nonneg_of_fin
    {n : ℕ} (clickThroughRate : ℕ → ℝ)
    (O : PositionOutcome (Fin n) (Fin n)) (i : Fin n)
    (hclick_nonneg : 0 ≤ clickThroughRate i.val)
    (hpayment_nonneg : 0 ≤ O.paymentPerClick i) :
    0 ≤ paper_theorem7_ranked_outcome_total_payment clickThroughRate O i.val := by
  simpa [paper_theorem7_ranked_outcome_total_payment_of_fin] using
    mul_nonneg hclick_nonneg hpayment_nonneg

/-
EOS Theorem 7 adjacent stable-assignment payment lower bound, expressed in
ranked total-payment coordinates. If ranks `k` and `k+1` are present and the
comparison outcome assigns each rank to its own slot, stability implies the
adjacent lower bound used by the VCG-tail induction.
-/
theorem paper_theorem7_ranked_adjacent_total_payment_lower_bound_of_stable
    {n : ℕ} {value clickThroughRate : ℕ → ℝ}
    (O : PositionOutcome (Fin n) (Fin n)) {k : ℕ}
    (hk : k + 1 < n)
    (hstable :
      O.StableAssignment
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun i : Fin n => value i.val))
    (hslots : ∀ i : Fin n, O.slotOf i = some i) :
    (clickThroughRate k - clickThroughRate (k + 1)) * value (k + 1) +
        paper_theorem7_ranked_outcome_total_payment
          clickThroughRate O (k + 1) ≤
      paper_theorem7_ranked_outcome_total_payment
        clickThroughRate O k := by
  let i : Fin n := ⟨k, Nat.lt_trans (Nat.lt_succ_self k) hk⟩
  let j : Fin n := ⟨k + 1, hk⟩
  have hpair :
      (clickThroughRate k - clickThroughRate (k + 1)) * value (k + 1) +
          clickThroughRate (k + 1) * O.paymentPerClick j ≤
        clickThroughRate k * O.paymentPerClick i := by
    simpa [paper_theorem7_ranked_environment, i, j] using
      paper_position_stable_assignment_payment_lower_bound_pair
        (paper_theorem7_ranked_environment clickThroughRate)
        O (fun r : Fin n => value r.val)
        hstable i j (hslots i) (hslots j)
  simpa [paper_theorem7_ranked_outcome_total_payment,
    Nat.lt_trans (Nat.lt_succ_self k) hk, hk, i, j] using hpair

/-
EOS Theorem 7 finite VCG-tail payment lower bound from a stable ranked
comparison outcome. This is the main finite lower-bound bridge: stability gives
the adjacent total-payment inequalities, and the tail induction converts them
into a VCG-tail lower bound.
-/
theorem paper_theorem7_ranked_vcg_tail_payment_le_of_stable_assignment
    {n : ℕ} {value clickThroughRate : ℕ → ℝ}
    (O : PositionOutcome (Fin n) (Fin n)) (i : Fin n) (remaining : ℕ)
    (hbound : i.val + remaining < n)
    (hstable :
      O.StableAssignment
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun r : Fin n => value r.val))
    (hslots : ∀ r : Fin n, O.slotOf r = some r)
    (hterminal :
      0 ≤
        paper_theorem7_ranked_outcome_total_payment
          clickThroughRate O (i.val + remaining)) :
    paper_theorem7_ranked_vcg_tail_payment
        value clickThroughRate i.val remaining ≤
      paper_theorem7_ranked_outcome_total_payment
        clickThroughRate O i.val := by
  exact
    paper_theorem7_ranked_vcg_tail_payment_le_of_adjacent_total_bounds
      value clickThroughRate
      (paper_theorem7_ranked_outcome_total_payment clickThroughRate O)
      i.val remaining hterminal
      (by
        intro k _hkge hklt
        have hk_succ : k + 1 < n := by
          exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hklt) hbound
        exact
          paper_theorem7_ranked_adjacent_total_payment_lower_bound_of_stable
            O hk_succ hstable hslots)

/-
EOS Theorem 7 per-click finite VCG-tail lower bound from a stable ranked
comparison outcome. With positive click-through rate at rank `i`, the
click-weighted lower bound divides through to a per-click lower bound.
-/
theorem paper_theorem7_ranked_vcg_tail_payment_per_click_le_of_stable_assignment
    {n : ℕ} {value clickThroughRate : ℕ → ℝ}
    (O : PositionOutcome (Fin n) (Fin n)) (i : Fin n) (remaining : ℕ)
    (hclick_pos : 0 < clickThroughRate i.val)
    (hbound : i.val + remaining < n)
    (hstable :
      O.StableAssignment
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun r : Fin n => value r.val))
    (hslots : ∀ r : Fin n, O.slotOf r = some r)
    (hterminal :
      0 ≤
        paper_theorem7_ranked_outcome_total_payment
          clickThroughRate O (i.val + remaining)) :
    paper_theorem7_ranked_vcg_tail_payment
        value clickThroughRate i.val remaining / clickThroughRate i.val ≤
      O.paymentPerClick i := by
  have htail :
      paper_theorem7_ranked_vcg_tail_payment
          value clickThroughRate i.val remaining ≤
        clickThroughRate i.val * O.paymentPerClick i := by
    simpa [paper_theorem7_ranked_outcome_total_payment_of_fin] using
      paper_theorem7_ranked_vcg_tail_payment_le_of_stable_assignment
        O i remaining hbound hstable hslots hterminal
  exact (div_le_iff₀ hclick_pos).mpr (by simpa [mul_comm] using htail)

/-
EOS Theorem 7 direct `B*` payment lower bound from a stable ranked comparison
outcome. If the VCG total-payment input to `B*` agrees with the finite VCG-tail
payment at rank `i`, then the `B*` per-click payment is weakly below the
comparison outcome's per-click payment.
-/
theorem paper_theorem7_ranked_bstar_payment_le_of_stable_assignment_tail
    {n : ℕ} {value vcgTotalPayment clickThroughRate : ℕ → ℝ}
    (O : PositionOutcome (Fin n) (Fin n)) (i : Fin n) (remaining : ℕ)
    (hvcg_i :
      vcgTotalPayment i.val =
        paper_theorem7_ranked_vcg_tail_payment
          value clickThroughRate i.val remaining)
    (hclick_pos : 0 < clickThroughRate i.val)
    (hbound : i.val + remaining < n)
    (hstable :
      O.StableAssignment
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun r : Fin n => value r.val))
    (hslots : ∀ r : Fin n, O.slotOf r = some r)
    (hterminal :
      0 ≤
        paper_theorem7_ranked_outcome_total_payment
          clickThroughRate O (i.val + remaining)) :
    (paper_theorem7_ranked_bstar_outcome
      value vcgTotalPayment clickThroughRate).paymentPerClick i ≤
      O.paymentPerClick i := by
  have htail :
      paper_theorem7_ranked_vcg_tail_payment
          value clickThroughRate i.val remaining / clickThroughRate i.val ≤
        O.paymentPerClick i :=
    paper_theorem7_ranked_vcg_tail_payment_per_click_le_of_stable_assignment
      O i remaining hclick_pos hbound hstable hslots hterminal
  simpa [paper_theorem7_ranked_bstar_outcome,
    paper_theorem7_bstar_bid, hvcg_i] using htail

/-
EOS Theorem 7 canonical finite-tail length for rank `i` among `n` ranked
positions: the number of lower positions strictly below rank `i`.
-/
def paper_theorem7_ranked_canonical_tail_remaining
    {n : ℕ} (i : Fin n) : ℕ :=
  n - (i.val + 1)

/-
EOS Theorem 7 canonical finite-tail bound. Starting at any finite rank `i`,
the canonical tail endpoint remains inside the finite ranked position set.
-/
theorem paper_theorem7_ranked_canonical_tail_remaining_bound
    {n : ℕ} (i : Fin n) :
    i.val + paper_theorem7_ranked_canonical_tail_remaining i < n := by
  have hsucc : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
  have hlt :
      i.val + (n - (i.val + 1)) <
        (i.val + 1) + (n - (i.val + 1)) :=
    Nat.add_lt_add_right (Nat.lt_succ_self i.val)
      (n - (i.val + 1))
  simpa [paper_theorem7_ranked_canonical_tail_remaining,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    Nat.add_sub_of_le hsucc] using hlt

/-
EOS Theorem 7 canonical terminal total-payment nonnegativity from ordinary
nonnegative comparison payments. This packages the terminal side condition
needed by the finite-tail lower-bound induction into the paper-level payment
sign convention.
-/
theorem paper_theorem7_ranked_canonical_terminal_total_payment_nonneg_of_payments_nonneg
    {n : ℕ} (clickThroughRate : ℕ → ℝ)
    (O : PositionOutcome (Fin n) (Fin n))
    (hclick_nonneg : ∀ i : Fin n, 0 ≤ clickThroughRate i.val)
    (hpayment_nonneg : ∀ i : Fin n, 0 ≤ O.paymentPerClick i)
    (i : Fin n) :
    0 ≤
      paper_theorem7_ranked_outcome_total_payment clickThroughRate O
        (i.val + paper_theorem7_ranked_canonical_tail_remaining i) := by
  let terminal : Fin n :=
    ⟨i.val + paper_theorem7_ranked_canonical_tail_remaining i,
      paper_theorem7_ranked_canonical_tail_remaining_bound i⟩
  simpa [terminal] using
    paper_theorem7_ranked_outcome_total_payment_nonneg_of_fin
      clickThroughRate O terminal
      (hclick_nonneg terminal) (hpayment_nonneg terminal)

/-
EOS Theorem 7 ranked `B*` outcome payment nonnegativity under canonical
finite-tail VCG payments. This gives a direct audit handle for the sign
convention on the constructed equilibrium payments.
-/
theorem paper_theorem7_ranked_bstar_outcome_payment_nonneg_of_canonical_vcg_tail
    {n : ℕ} {value vcgTotalPayment clickThroughRate : ℕ → ℝ}
    (hvalue_nonneg : ∀ i, 0 ≤ value i)
    (hclick_pos : ∀ i : Fin n, 0 < clickThroughRate i.val)
    (hclick_mono : ∀ i, clickThroughRate (i + 1) ≤ clickThroughRate i)
    (hvcg_tail_eq :
      ∀ i : Fin n,
        vcgTotalPayment i.val =
          paper_theorem7_ranked_vcg_tail_payment
            value clickThroughRate i.val
            (paper_theorem7_ranked_canonical_tail_remaining i))
    (i : Fin n) :
    0 ≤
      (paper_theorem7_ranked_bstar_outcome
        value vcgTotalPayment clickThroughRate).paymentPerClick i := by
  have hvcg_nonneg : 0 ≤ vcgTotalPayment i.val := by
    rw [hvcg_tail_eq i]
    exact
      paper_theorem7_ranked_vcg_tail_payment_nonneg
        hvalue_nonneg hclick_mono i.val
        (paper_theorem7_ranked_canonical_tail_remaining i)
  simpa [paper_theorem7_ranked_bstar_outcome, paper_theorem7_bstar_bid] using
    div_nonneg hvcg_nonneg (le_of_lt (hclick_pos i))

/-
EOS Theorem 7 ranked `B*` outcome has no positive transfers under the canonical
finite-tail VCG-payment assumptions. This packages payment nonnegativity in the
paper-native position-auction sign convention.
-/
theorem paper_theorem7_ranked_bstar_outcome_no_positive_transfers_of_canonical_vcg_tail
    {n : ℕ} {value vcgTotalPayment clickThroughRate : ℕ → ℝ}
    (hvalue_nonneg : ∀ i, 0 ≤ value i)
    (hclick_pos : ∀ i : Fin n, 0 < clickThroughRate i.val)
    (hclick_mono : ∀ i, clickThroughRate (i + 1) ≤ clickThroughRate i)
    (hvcg_tail_eq :
      ∀ i : Fin n,
        vcgTotalPayment i.val =
          paper_theorem7_ranked_vcg_tail_payment
            value clickThroughRate i.val
            (paper_theorem7_ranked_canonical_tail_remaining i)) :
    paper_position_no_positive_transfers
      (paper_theorem7_ranked_bstar_outcome (n := n)
        value vcgTotalPayment clickThroughRate) := by
  intro i
  exact
    paper_theorem7_ranked_bstar_outcome_payment_nonneg_of_canonical_vcg_tail
      hvalue_nonneg hclick_pos hclick_mono hvcg_tail_eq i

/-
EOS Theorem 7 canonical finite VCG total-payment sequence for `n` ranked
positions.
-/
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

/-
EOS Theorem 7 canonical finite-tail comparison-payment certificate form. The
ranked `B*` outcome is locally envy-free, stable, VCG-equivalent, and weakly
revenue-minimal among same-assignment locally envy-free comparison outcomes
whose per-click payments are nonnegative.
-/
theorem paper_theorem7_ordered_ranked_canonical_tail_no_positive_transfer_paper_conclusion
    {n : ℕ}
    (model :
      PaperTheorem7OrderedRankedCanonicalTailComparisonPaymentCertificate n)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i) :
    ∃ O : PositionOutcome (Fin n) (Fin n),
      paper_position_no_positive_transfers O ∧
        O.SlotEnvyFree
          (paper_theorem7_ranked_environment model.clickThroughRate)
          (fun i : Fin n => model.value i.val) ∧
        O.StableAssignment
          (paper_theorem7_ranked_environment model.clickThroughRate)
          (fun i : Fin n => model.value i.val) ∧
        (∀ i, O.slotOf i = model.vcgOutcome.slotOf i) ∧
        (∀ i, O.paymentPerClick i = model.vcgOutcome.paymentPerClick i) ∧
        ∀ other : PositionOutcome (Fin n) (Fin n),
          other.FeasibleAssignment →
          other.IndividuallyRational
            (paper_theorem7_ranked_environment model.clickThroughRate)
            (fun i : Fin n => model.value i.val) →
          other.SlotEnvyFree
            (paper_theorem7_ranked_environment model.clickThroughRate)
            (fun i : Fin n => model.value i.val) →
            (∀ i, O.slotOf i = other.slotOf i) →
              paper_position_no_positive_transfers other →
                O.revenue
                    (paper_theorem7_ranked_environment model.clickThroughRate) ≤
                  other.revenue
                    (paper_theorem7_ranked_environment model.clickThroughRate) := by
  let O : PositionOutcome (Fin n) (Fin n) :=
    paper_theorem7_ranked_bstar_outcome (n := n)
      model.value model.vcgTotalPayment model.clickThroughRate
  have hclick_ne : ∀ i : Fin n, model.clickThroughRate i.val ≠ 0 :=
    fun i => ne_of_gt (model.click_pos i)
  have hnpt : paper_position_no_positive_transfers O := by
    simpa [O] using
      paper_theorem7_ranked_bstar_outcome_no_positive_transfers_of_canonical_vcg_tail
        hvalue_nonneg model.click_pos model.click_mono model.vcg_tail_eq
  have hlef :
      O.SlotEnvyFree
        (paper_theorem7_ranked_environment model.clickThroughRate)
        (fun i : Fin n => model.value i.val) :=
    paper_theorem7_ranked_bstar_outcome_slot_envy_free_of_ordered_values
      hclick_ne model.click_mono model.value_mono model.vcg_rec
  have hstable :
      O.StableAssignment
        (paper_theorem7_ranked_environment model.clickThroughRate)
        (fun i : Fin n => model.value i.val) :=
    paper_theorem7_ranked_bstar_outcome_stable_assignment_of_ordered_values
      hclick_ne model.click_mono model.value_mono model.vcg_rec
      model.payment_le_value
  refine ⟨O, hnpt, hlef, hstable, model.same_slots_as_vcg,
    model.same_payments_as_vcg, ?_⟩
  intro other hfeasible hIR hother hsame hnpt_other
  have hstable_other :
      other.StableAssignment
        (paper_theorem7_ranked_environment model.clickThroughRate)
        (fun i : Fin n => model.value i.val) :=
    paper_position_slot_envy_free_stable_assignment
      (paper_theorem7_ranked_environment model.clickThroughRate)
      other (fun i : Fin n => model.value i.val)
      hfeasible hIR hother
  have hslots : ∀ i : Fin n, other.slotOf i = some i := by
    intro i
    simpa [O, paper_theorem7_ranked_bstar_outcome] using (hsame i).symm
  have hpay_le : ∀ i : Fin n, O.paymentPerClick i ≤ other.paymentPerClick i := by
    intro i
    exact
      paper_theorem7_ranked_bstar_payment_le_of_stable_assignment_tail
        other i (paper_theorem7_ranked_canonical_tail_remaining i)
        (model.vcg_tail_eq i) (model.click_pos i)
        (paper_theorem7_ranked_canonical_tail_remaining_bound i)
        hstable_other hslots
        (paper_theorem7_ranked_canonical_terminal_total_payment_nonneg_of_payments_nonneg
          model.clickThroughRate other model.click_nonneg hnpt_other i)
  exact
    paper_position_revenue_le_of_same_slots_payment_le
      (paper_theorem7_ranked_environment model.clickThroughRate)
      O other model.click_nonneg hsame hpay_le

/-
EOS Theorem 7 `B*` payment identity specialized to finite VCG tail payments.
If rank `i` pays the next `B*` bid per click, its total payment is the finite
tail-payment value for rank `i`.
-/
noncomputable def paper_theorem8_generalized_english_indifference_price
    (alphaAbove alphaCurrent lastDropout value : ℝ) : ℝ :=
  value - (alphaCurrent / alphaAbove) * (value - lastDropout)

/-
EOS Theorem 8 indifference algebra:
`alphaAbove * (value - q) = alphaCurrent * (value - lastDropout)`.
-/
noncomputable def paper_theorem8_generalized_english_ranked_dropout_price
    (clickThroughRate lastDropout value : ℕ → ℝ) (rank : ℕ) : ℝ :=
  paper_theorem8_generalized_english_indifference_price
    (clickThroughRate rank) (clickThroughRate (rank + 1))
    (lastDropout rank) (value (rank + 1))

/-
EOS Theorem 8 ranked continuity algebra: holding the history and all other
values fixed, the rank-indexed dropout price is continuous in the valuation of
the bidder currently considering rank `rank + 1`.
-/
structure PaperTheorem8GeneralizedEnglishAuctionState (Bidder : Type*) where
  clockPrice : ℝ
  lastDropout : Bidder → Option ℝ

namespace PaperTheorem8GeneralizedEnglishAuctionState

/- A bidder is active exactly when no dropout price has been recorded. -/
def IsActive {Bidder : Type*}
    (state : PaperTheorem8GeneralizedEnglishAuctionState Bidder)
    (bidder : Bidder) : Prop :=
  state.lastDropout bidder = none

/- A bidder has dropped at price `price` when that price is recorded. -/
def advanceClock {Bidder : Type*}
    (state : PaperTheorem8GeneralizedEnglishAuctionState Bidder)
    (newPrice : ℝ) : PaperTheorem8GeneralizedEnglishAuctionState Bidder where
  clockPrice := newPrice
  lastDropout := state.lastDropout

/- Advancing the clock sets the clock price to the requested new price. -/
def recordDropout {Bidder : Type*} [DecidableEq Bidder]
    (state : PaperTheorem8GeneralizedEnglishAuctionState Bidder)
    (bidder : Bidder) : PaperTheorem8GeneralizedEnglishAuctionState Bidder where
  clockPrice := state.clockPrice
  lastDropout j := if j = bidder then some state.clockPrice else state.lastDropout j

/- Recording a dropout makes that bidder dropped at the current clock price. -/
inductive StrategyStep
    {Bidder : Type*} [DecidableEq Bidder]
    (strategy :
      PaperTheorem8GeneralizedEnglishAuctionState Bidder → Bidder → Prop) :
    PaperTheorem8GeneralizedEnglishAuctionState Bidder →
      PaperTheorem8GeneralizedEnglishAuctionState Bidder → Prop
  | advance (state : PaperTheorem8GeneralizedEnglishAuctionState Bidder)
      (newPrice : ℝ) :
      state.clockPrice ≤ newPrice →
        StrategyStep strategy state (advanceClock state newPrice)
  | dropout (state : PaperTheorem8GeneralizedEnglishAuctionState Bidder)
      (bidder : Bidder) :
      state.IsActive bidder →
        strategy state bidder →
          StrategyStep strategy state (recordDropout state bidder)

/- Every strategy-consistent transition is a concrete transition. -/
inductive StrategyHistory
    {Bidder : Type*} [DecidableEq Bidder]
    (strategy :
      PaperTheorem8GeneralizedEnglishAuctionState Bidder → Bidder → Prop) :
    PaperTheorem8GeneralizedEnglishAuctionState Bidder →
      PaperTheorem8GeneralizedEnglishAuctionState Bidder → Prop
  | refl (state : PaperTheorem8GeneralizedEnglishAuctionState Bidder) :
      StrategyHistory strategy state state
  | cons {state mid finalState :
        PaperTheorem8GeneralizedEnglishAuctionState Bidder} :
      StrategyStep strategy state mid →
        StrategyHistory strategy mid finalState →
          StrategyHistory strategy state finalState

/- Every strategy-consistent history is a concrete history. -/
theorem StrategyHistory.trans
    {Bidder : Type*} [DecidableEq Bidder]
    {strategy :
      PaperTheorem8GeneralizedEnglishAuctionState Bidder → Bidder → Prop}
    {state mid finalState : PaperTheorem8GeneralizedEnglishAuctionState Bidder}
    (hfirst : StrategyHistory strategy state mid)
    (hsecond : StrategyHistory strategy mid finalState) :
    StrategyHistory strategy state finalState := by
  induction hfirst with
  | refl state =>
      exact hsecond
  | cons hstep hhist ih =>
      exact StrategyHistory.cons hstep (ih hsecond)

/- Strategy-consistent histories have weakly increasing clocks. -/
end PaperTheorem8GeneralizedEnglishAuctionState

/-
EOS Theorem 8 generalized-English pure dropout strategy: at a state, a bidder
either drops (`True`) or remains active (`False`).
-/
abbrev PaperTheorem8GeneralizedEnglishStrategy (Bidder : Type*) :=
  PaperTheorem8GeneralizedEnglishAuctionState Bidder → Bidder → Prop

/-
EOS Theorem 8 threshold dropout strategy. Bidder `i` drops once the clock price
reaches the bidder's threshold.
-/
def paper_theorem8_threshold_dropout_strategy
    {Bidder : Type*} (dropoutPrice : Bidder → ℝ) :
    PaperTheorem8GeneralizedEnglishStrategy Bidder :=
  fun state bidder => dropoutPrice bidder ≤ state.clockPrice

/- The threshold strategy drops exactly at or above the threshold price. -/
def paper_theorem8_ranked_threshold_dropout_strategy
    (clickThroughRate lastDropout value : ℕ → ℝ) :
    PaperTheorem8GeneralizedEnglishStrategy ℕ :=
  paper_theorem8_threshold_dropout_strategy
    (fun rank =>
      paper_theorem8_generalized_english_ranked_dropout_price
        clickThroughRate lastDropout value rank)

/- The ranked threshold strategy drops exactly at or above the ranked formula. -/
structure PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate where
  clickThroughRate : ℕ → ℝ
  value : ℕ → ℝ
  remaining : ℕ
  click_pos : ∀ rank, 0 < clickThroughRate rank
  current_nonneg : ∀ rank, 0 ≤ clickThroughRate (rank + 1)
  current_le : ∀ rank, clickThroughRate (rank + 1) ≤ clickThroughRate rank
  continuation_bstar_le_value : ∀ rank,
    paper_theorem7_bstar_bid value
      (fun j =>
        paper_theorem7_ranked_vcg_tail_payment
          value clickThroughRate j remaining)
      clickThroughRate (rank + 2) ≤ value (rank + 1)

/-
Standard ordered-rank assumptions for the exact finite `B*` ranked-threshold
strategy in EOS Theorem 8.
-/
noncomputable def paper_theorem8_bstar_threshold_bid
    (value clickThroughRate : ℕ → ℝ) (remaining rank : ℕ) : ℝ :=
  paper_theorem7_bstar_bid value
    (fun j =>
      paper_theorem7_ranked_vcg_tail_payment
        value clickThroughRate j remaining)
    clickThroughRate rank

/-
The continuation finite `B*` threshold is weakly below the current finite
`B*` dropout threshold. This is the shifted Theorem 8 bridge induced by the
Theorem 7 VCG-tail recursion: the lower adjacent slot's continuation bid from
tail length `remaining` is at most the current dropout threshold from tail
length `remaining + 1`.
-/
noncomputable def paper_theorem8_bstar_ranked_threshold_strategy
    (value clickThroughRate : ℕ → ℝ) (remaining : ℕ) :
    PaperTheorem8GeneralizedEnglishStrategy ℕ :=
  paper_theorem8_ranked_threshold_dropout_strategy
    clickThroughRate
    (fun k =>
      paper_theorem8_bstar_threshold_bid
        value clickThroughRate remaining (k + 2))
    value

/-
The exact finite `B*` ranked-threshold strategy drops exactly when the clock
reaches the current finite `B*` threshold bid.
-/
namespace PaperTheorem8GeneralizedEnglishDynamicGame

/-
Perfect Bayesian equilibrium for the abstract generalized-English dynamic-game
interface: there exists a belief system under which the strategy profile is
both belief-consistent and sequentially rational.
-/
end PaperTheorem8GeneralizedEnglishDynamicGame

/-
Paper-facing expansion of the abstract generalized-English PBE predicate:
checking PBE is exactly checking that one belief system witnesses both
consistency and sequential rationality.
-/
inductive PaperTheorem8BStarRankedThresholdExactDropHistory
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate) :
    PaperTheorem8GeneralizedEnglishAuctionState ℕ →
      PaperTheorem8GeneralizedEnglishAuctionState ℕ → Prop
  | refl (state : PaperTheorem8GeneralizedEnglishAuctionState ℕ) :
      PaperTheorem8BStarRankedThresholdExactDropHistory model state state
  | advance {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
      (newPrice : ℝ) :
      state.clockPrice ≤ newPrice →
        PaperTheorem8BStarRankedThresholdExactDropHistory model
          (PaperTheorem8GeneralizedEnglishAuctionState.advanceClock state newPrice)
          finalState →
        PaperTheorem8BStarRankedThresholdExactDropHistory model state finalState
  | dropout {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
      (rank : ℕ) :
      state.IsActive rank →
        state.clockPrice =
          paper_theorem8_bstar_threshold_bid
            model.value model.clickThroughRate (model.remaining + 1)
            (rank + 1) →
        PaperTheorem8BStarRankedThresholdExactDropHistory model
          (PaperTheorem8GeneralizedEnglishAuctionState.recordDropout state rank)
          finalState →
        PaperTheorem8BStarRankedThresholdExactDropHistory model state finalState

/- Exact finite-`B*` drop histories compose. This lets auditors build a
finite source history from individually checked exact-drop segments. -/
theorem PaperTheorem8BStarRankedThresholdExactDropHistory.trans
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state midState finalState :
      PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hleft :
      PaperTheorem8BStarRankedThresholdExactDropHistory model state midState)
    (hright :
      PaperTheorem8BStarRankedThresholdExactDropHistory model midState finalState) :
    PaperTheorem8BStarRankedThresholdExactDropHistory model state finalState := by
  induction hleft with
  | refl state =>
      exact hright
  | @advance state0 midState0 newPrice hclock htail ih =>
      exact
        PaperTheorem8BStarRankedThresholdExactDropHistory.advance
          newPrice hclock (ih hright)
  | @dropout state0 midState0 rank hactive hclock htail ih =>
      exact
        PaperTheorem8BStarRankedThresholdExactDropHistory.dropout
          rank hactive hclock (ih hright)

/-
Every finite-`B*` exact-drop history is an ordinary strategy-consistent history
for the named finite-`B*` ranked-threshold strategy.
-/
inductive PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate) :
    PaperTheorem8GeneralizedEnglishAuctionState ℕ →
      PaperTheorem8GeneralizedEnglishAuctionState ℕ → Prop
  | refl (state : PaperTheorem8GeneralizedEnglishAuctionState ℕ) :
      PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory model state state
  | advance {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
      (newPrice : ℝ) :
      state.clockPrice ≤ newPrice →
        PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory model
          (PaperTheorem8GeneralizedEnglishAuctionState.advanceClock state newPrice)
          finalState →
        PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory model
          state finalState
  | dropout {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
      (rank : ℕ) :
      state.IsActive rank →
        paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining state rank →
        state.clockPrice ≤
          paper_theorem8_bstar_threshold_bid
            model.value model.clickThroughRate (model.remaining + 1)
            (rank + 1) →
        PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory model
          (PaperTheorem8GeneralizedEnglishAuctionState.recordDropout state rank)
          finalState →
        PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory model
          state finalState

/- No-overshoot source histories compose. -/
theorem PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory.trans
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state midState finalState :
      PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hfirst :
      PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
        model state midState)
    (hsecond :
      PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
        model midState finalState) :
    PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
      model state finalState := by
  induction hfirst with
  | refl state =>
      exact hsecond
  | @advance state0 midState0 newPrice hclock htail ih =>
      exact
        PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory.advance
          newPrice hclock (ih hsecond)
  | @dropout state0 midState0 rank hactive hstrategy hno_overshoot htail ih =>
      exact
        PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory.dropout
          rank hactive hstrategy hno_overshoot (ih hsecond)

/-
Source-semantic timing statement for the remaining Theorem 8 source proof.  At
every realized new-dropout transition under the named finite `B*` strategy, the
pre-dropout clock has not overshot the dropping rank's finite `B*` threshold.
Behavioral optimality/tie-breaking do not imply this statement by themselves;
it is the concrete source-transition invariant needed by the exact-record
machinery.
-/
inductive PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate) :
    PaperTheorem8GeneralizedEnglishAuctionState ℕ →
      PaperTheorem8GeneralizedEnglishAuctionState ℕ → Prop
  | refl (state : PaperTheorem8GeneralizedEnglishAuctionState ℕ) :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model state state
  | advance {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
      (newPrice : ℝ) :
      state.clockPrice ≤ newPrice →
        (∀ rank,
          state.IsActive rank →
            newPrice ≤
              paper_theorem8_bstar_threshold_bid
                model.value model.clickThroughRate (model.remaining + 1)
                (rank + 1)) →
          PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
            model
            (PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
              state newPrice)
            finalState →
            PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
              model state finalState
  | dropout {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
      (rank : ℕ) :
      state.IsActive rank →
        paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining state rank →
          PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
            model
            (PaperTheorem8GeneralizedEnglishAuctionState.recordDropout
              state rank)
            finalState →
            PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
              model state finalState

/- Clock-disciplined source histories compose. -/
theorem PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory.trans
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state midState finalState :
      PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hfirst :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model state midState)
    (hsecond :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model midState finalState) :
    PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
      model state finalState := by
  induction hfirst with
  | refl state =>
      exact hsecond
  | @advance state0 midState0 newPrice hclock hsafe htail ih =>
      exact
        PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory.advance
          newPrice hclock hsafe (ih hsecond)
  | @dropout state0 midState0 rank hactive hstrategy htail ih =>
      exact
        PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory.dropout
          rank hactive hstrategy (ih hsecond)

/-
Single-step source-transition form of clock discipline for the named finite
`B*` strategy. An advance step may only move the clock to a price that does not
pass any currently active rank's finite `B*` threshold; a dropout step is the
ordinary named-strategy dropout transition.
-/
inductive PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyStep
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate) :
    PaperTheorem8GeneralizedEnglishAuctionState ℕ →
      PaperTheorem8GeneralizedEnglishAuctionState ℕ → Prop
  | advance (state : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
      (newPrice : ℝ) :
      state.clockPrice ≤ newPrice →
        (∀ rank,
          state.IsActive rank →
            newPrice ≤
              paper_theorem8_bstar_threshold_bid
                model.value model.clickThroughRate (model.remaining + 1)
                (rank + 1)) →
          PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyStep
            model state
            (PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
              state newPrice)
  | dropout (state : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
      (rank : ℕ) :
      state.IsActive rank →
        paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining state rank →
          PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyStep
            model state
            (PaperTheorem8GeneralizedEnglishAuctionState.recordDropout
              state rank)

/-
Every clock-disciplined source step is an ordinary strategy-consistent step for
the named finite `B*` strategy.
-/
inductive PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate) :
    PaperTheorem8GeneralizedEnglishAuctionState ℕ →
      PaperTheorem8GeneralizedEnglishAuctionState ℕ → Prop
  | refl (state : PaperTheorem8GeneralizedEnglishAuctionState ℕ) :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model state state
  | cons {state mid finalState :
        PaperTheorem8GeneralizedEnglishAuctionState ℕ} :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyStep
        model state mid →
          PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
            model mid finalState →
          PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
            model state finalState

/- Finite traces of clock-disciplined source steps compose. -/
theorem PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace.trans
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state midState finalState :
      PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hfirst :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model state midState)
    (hsecond :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model midState finalState) :
    PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
      model state finalState := by
  induction hfirst with
  | refl state =>
      exact hsecond
  | @cons state midState finalState hstep htail ih =>
      exact
        PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace.cons
          hstep (ih hsecond)

/-
A clock-disciplined source step is the corresponding one-step finite trace.
This lets source proofs assemble explicit traces from local transition checks.
-/
end Auction
end EconCSLib
