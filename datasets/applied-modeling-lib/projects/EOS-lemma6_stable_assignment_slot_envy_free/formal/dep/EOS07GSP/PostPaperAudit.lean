import dep.EconCSLib.MechanismDesign.Auctions.MainTheorems
namespace EOS07GSP
open EconCSLib.Auction
noncomputable section
theorem audit_lemma6_stable_assignment_slot_envy_free
    {Bidder Slot : Type*}
    (E : PositionEnvironment Slot)
    (O : PositionOutcome Bidder Slot) (values : Bidder → ℝ)
    (h : O.StableAssignment E values) :
    O.SlotEnvyFree E values := by
  exact paper_position_stable_assignment_slot_envy_free E O values h

/- Audit for Theorem 7 `B*` payment identity: the next `B*` bid reproduces
the VCG total payment for the current rank. -/

end
end EOS07GSP
