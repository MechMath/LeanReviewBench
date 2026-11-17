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
theorem paper_position_locally_envy_free_equilibrium_stable_assignment
    {Bidder Slot : Type*} [DecidableEq Bidder]
    (E : PositionEnvironment Slot) (M : PositionMechanism Bidder Slot)
    (values bids : Bidder → ℝ)
    (hfeasible : (M bids).FeasibleAssignment)
    (hIR : (M bids).IndividuallyRational E values)
    (h : M.LocallyEnvyFreeEquilibrium E values bids) :
    (M bids).StableAssignment E values := by
  exact
    paper_position_slot_envy_free_stable_assignment
      E (M bids) values hfeasible hIR h.2

/-
EOS Lemma 6 outcome-level converse bridge. In the formal assignment-game
predicate, stability already includes the no-profitable-rematch inequalities,
so it gives the locally envy-free outcome condition.
-/
namespace PaperTheorem8GeneralizedEnglishAuctionState

/- A bidder is active exactly when no dropout price has been recorded. -/
end PaperTheorem8GeneralizedEnglishAuctionState

/-
EOS Theorem 8 generalized-English pure dropout strategy: at a state, a bidder
either drops (`True`) or remains active (`False`).
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
end Auction
end EconCSLib
