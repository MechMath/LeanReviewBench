import dep.EconCSLib.MechanismDesign.Auctions.MainTheorems
namespace EOS07GSP
open EconCSLib.Auction
noncomputable section
theorem audit_lemma5_locally_envy_free_equilibrium_stable_assignment
    {Bidder Slot : Type*} [DecidableEq Bidder]
    (E : PositionEnvironment Slot) (M : PositionMechanism Bidder Slot)
    (values bids : Bidder → ℝ)
    (hfeasible : (M bids).FeasibleAssignment)
    (hIR : (M bids).IndividuallyRational E values)
    (h : M.LocallyEnvyFreeEquilibrium E values bids) :
    (M bids).StableAssignment E values := by
  exact
    paper_position_locally_envy_free_equilibrium_stable_assignment
      E M values bids hfeasible hIR h

/- Audit for Lemma 6 caveat boundary: the formal stable-assignment predicate
contains the no-profitable-rematch inequalities needed for slot envy-freeness. -/

end
end EOS07GSP
