import dep.EconCSLib.MechanismDesign.Auctions.MainTheorems
namespace EOS07GSP
open EconCSLib.Auction
noncomputable section
theorem audit_theorem7_ordered_ranked_canonical_tail_no_positive_transfer_paper_conclusion
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
  exact
    paper_theorem7_ordered_ranked_canonical_tail_no_positive_transfer_paper_conclusion
      model hvalue_nonneg

/- Audit for Theorem 7 finite VCG-tail payments: under monotone click-through
rates and nonnegative values, every finite tail-payment prefix is nonnegative. -/

end
end EOS07GSP
