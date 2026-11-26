import Mathlib
import dep.EconCSLib.MechanismDesign.Auctions.Position

namespace EOS07GSP.PaperInterface

abbrev lemma6_stable_assignment_slot_envy_free.{u_1, u_2} : ∀ {Bidder : Type u_1} {Slot : Type u_2} (E : EconCSLib.Auction.PositionEnvironment.{u_2} Slot)
  (O : EconCSLib.Auction.PositionOutcome.{u_1, u_2} Bidder Slot) (values : Bidder → Real)
  (h : @EconCSLib.Auction.PositionOutcome.StableAssignment.{u_1, u_2} Bidder Slot E O values),
  @EconCSLib.Auction.PositionOutcome.SlotEnvyFree.{u_1, u_2} Bidder Slot E O values := sorry

end EOS07GSP.PaperInterface
