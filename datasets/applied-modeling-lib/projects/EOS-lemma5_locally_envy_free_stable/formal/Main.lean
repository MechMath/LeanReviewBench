import Mathlib
import dep.EconCSLib.MechanismDesign.Auctions.Position

namespace EOS07GSP.PaperInterface

abbrev lemma5_locally_envy_free_stable.{u_1, u_2} : ∀ {Bidder : Type u_1} {Slot : Type u_2} [inst : DecidableEq.{u_1 + 1} Bidder]
  (E : EconCSLib.Auction.PositionEnvironment.{u_2} Slot)
  (M : EconCSLib.Auction.PositionMechanism.{u_1, u_2} Bidder Slot) (values bids : Bidder → Real)
  (hfeasible : @EconCSLib.Auction.PositionOutcome.FeasibleAssignment.{u_1, u_2} Bidder Slot (M bids))
  (hIR : @EconCSLib.Auction.PositionOutcome.IndividuallyRational.{u_1, u_2} Bidder Slot E (M bids) values)
  (h : @EconCSLib.Auction.PositionMechanism.LocallyEnvyFreeEquilibrium.{u_1, u_2} Bidder Slot inst E M values bids),
  @EconCSLib.Auction.PositionOutcome.StableAssignment.{u_1, u_2} Bidder Slot E (M bids) values := sorry

end EOS07GSP.PaperInterface
