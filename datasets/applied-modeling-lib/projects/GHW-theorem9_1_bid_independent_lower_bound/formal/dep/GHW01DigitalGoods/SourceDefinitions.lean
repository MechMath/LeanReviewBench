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
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import dep.EconCSLib.MechanismDesign.Auctions.DigitalGoods

namespace GHW01DigitalGoods

namespace SourceDefinitions

open EconCSLib.Auction

open scoped BigOperators ENNReal

noncomputable section

/-- An auction outcome is a finite set of satisfied bids and one sale price
for each bidder.  Prices of losing bidders are semantically irrelevant.

Source: lines 200-203.
-/
structure AuctionOutcome (Agent : Type*) where
  winners : Finset Agent
  salePrice : Agent → ℝ

namespace AuctionOutcome

/-- Auction revenue is the sum of all winning sale prices.

Source: lines 210-214.
-/
def revenue {Agent : Type*} (outcome : AuctionOutcome Agent) : ℝ :=
  ∑ i ∈ outcome.winners, outcome.salePrice i

end AuctionOutcome

end

end SourceDefinitions

end GHW01DigitalGoods
