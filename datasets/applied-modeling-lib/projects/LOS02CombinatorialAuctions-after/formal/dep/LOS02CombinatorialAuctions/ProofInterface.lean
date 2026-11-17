import Cslib.Foundations.Data.RelatesInSteps
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Find
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Defs
import Mathlib.GroupTheory.Perm.List
import Mathlib.Order.WellFoundedSet
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import dep.EconCSLib.MechanismDesign.Auctions.Combinatorial
import dep.EconCSLib.SocialChoice.FairDivision.IndivisibleGoods
import dep.LOS02CombinatorialAuctions.MainTheorems

namespace LOS02CombinatorialAuctions

namespace ProofInterface

open EconCSLib.Auction

/-- Paper utility in a combinatorial auction. -/
abbrev utility {Bidder Item : Type*}
    (M : CombinatorialAuction Bidder Item)
    (values reports : CombinatorialReport Bidder Item) (i : Bidder) : ℝ :=
  LOS02CombinatorialAuctions.paper_combinatorial_utility M values reports i

/-- Truthfulness predicate for single-minded bid-profile mechanisms. -/
abbrev singleMindedTruthfulOn
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (admissible : (Bidder → SingleMindedBid Item) → Prop) : Prop :=
  M.TruthfulOn admissible

/-- Nonempty, nonnegative single-minded bid profiles. -/
abbrev nonnegativeNonemptySingleMindedProfile
    {Bidder Item : Type*} [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) : Prop :=
  SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile bids

/-- Definition 7.1: average amount per good for a single-minded bid. -/
noncomputable abbrev averageAmountPerGood {Item : Type*} [DecidableEq Item]
    (b : SingleMindedBid Item) : ℝ :=
  LOS02CombinatorialAuctions.paper_average_amount_per_good b

/-- The paper's concrete average-order greedy accepted-set mechanism. -/
noncomputable abbrev averageGreedyAcceptedMechanism
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder] :
    SingleMindedAcceptedMechanism Bidder Item :=
  LOS02CombinatorialAuctions.paper_average_greedy_accepted_mechanism
    (Bidder := Bidder) (Item := Item)

end ProofInterface

end LOS02CombinatorialAuctions
