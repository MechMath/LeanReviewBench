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
import dep.LOS02CombinatorialAuctions.ProofInterface

namespace LOS02CombinatorialAuctions

namespace PaperInterface

open EconCSLib.Auction

/-- Paper utility in a combinatorial auction. -/
abbrev utility {Bidder Item : Type*}
    (M : CombinatorialAuction Bidder Item)
    (values reports : CombinatorialReport Bidder Item) (i : Bidder) : ℝ :=
  LOS02CombinatorialAuctions.paper_combinatorial_utility M values reports i

/-- Definition 7.1: average amount per good for a single-minded bid. -/
noncomputable abbrev averageAmountPerGood {Item : Type*} [DecidableEq Item]
    (b : SingleMindedBid Item) : ℝ :=
  LOS02CombinatorialAuctions.paper_average_amount_per_good b

/-- Theorem 10.2 average-order greedy mechanism truthfulness. -/
abbrev theorem10_2_averageGreedy_truthful.{u_1, u_2} : ∀ {Bidder : Type u_1} {Item : Type u_2} [inst : Fintype.{u_1} Bidder] [inst_1 : DecidableEq.{u_2 + 1} Item]
  [inst_2 : LinearOrder.{u_1} Bidder],
  @LOS02CombinatorialAuctions.ProofInterface.singleMindedTruthfulOn.{u_1, u_2} Bidder Item
    (fun (a b : Bidder) => @LinearOrder.toDecidableEq.{u_1} Bidder inst_2 a b) inst_1
    (@LOS02CombinatorialAuctions.ProofInterface.averageGreedyAcceptedMechanism.{u_1, u_2} Bidder Item inst inst_1
      inst_2)
    (@LOS02CombinatorialAuctions.ProofInterface.nonnegativeNonemptySingleMindedProfile.{u_1, u_2} Bidder Item inst_1) := sorry

end PaperInterface

end LOS02CombinatorialAuctions
