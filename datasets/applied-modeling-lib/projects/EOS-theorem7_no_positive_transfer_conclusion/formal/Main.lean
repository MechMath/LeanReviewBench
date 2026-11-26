import Mathlib
import dep.EconCSLib.MechanismDesign.Auctions.MainTheorems
import dep.EconCSLib.MechanismDesign.Auctions.Position

namespace EOS07GSP.PaperInterface

abbrev theorem7_no_positive_transfer_conclusion : ∀ {n : Nat} (model : EconCSLib.Auction.PaperTheorem7OrderedRankedCanonicalTailComparisonPaymentCertificate n)
  (hvalue_nonneg :
    ∀ (i : Nat),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@EconCSLib.Auction.PaperTheorem7OrderedRankedCanonicalTailComparisonPaymentCertificate.value n model i)),
  @Exists.{1} (EconCSLib.Auction.PositionOutcome.{0, 0} (Fin n) (Fin n))
    fun (O : EconCSLib.Auction.PositionOutcome.{0, 0} (Fin n) (Fin n)) =>
    And (@EconCSLib.Auction.paper_position_no_positive_transfers.{0, 0} (Fin n) (Fin n) O)
      (And
        (@EconCSLib.Auction.PositionOutcome.SlotEnvyFree.{0, 0} (Fin n) (Fin n)
          (@EconCSLib.Auction.paper_theorem7_ranked_environment n
            (@EconCSLib.Auction.PaperTheorem7OrderedRankedCanonicalTailComparisonPaymentCertificate.clickThroughRate n
              model))
          O fun (i : Fin n) =>
          @EconCSLib.Auction.PaperTheorem7OrderedRankedCanonicalTailComparisonPaymentCertificate.value n model
            (@Fin.val n i))
        (And
          (@EconCSLib.Auction.PositionOutcome.StableAssignment.{0, 0} (Fin n) (Fin n)
            (@EconCSLib.Auction.paper_theorem7_ranked_environment n
              (@EconCSLib.Auction.PaperTheorem7OrderedRankedCanonicalTailComparisonPaymentCertificate.clickThroughRate n
                model))
            O fun (i : Fin n) =>
            @EconCSLib.Auction.PaperTheorem7OrderedRankedCanonicalTailComparisonPaymentCertificate.value n model
              (@Fin.val n i))
          (And
            (∀ (i : Fin n),
              @Eq.{1} (Option.{0} (Fin n)) (@EconCSLib.Auction.PositionOutcome.slotOf.{0, 0} (Fin n) (Fin n) O i)
                (@EconCSLib.Auction.PositionOutcome.slotOf.{0, 0} (Fin n) (Fin n)
                  (@EconCSLib.Auction.PaperTheorem7OrderedRankedCanonicalTailComparisonPaymentCertificate.vcgOutcome n
                    model)
                  i))
            (And
              (∀ (i : Fin n),
                @Eq.{1} Real (@EconCSLib.Auction.PositionOutcome.paymentPerClick.{0, 0} (Fin n) (Fin n) O i)
                  (@EconCSLib.Auction.PositionOutcome.paymentPerClick.{0, 0} (Fin n) (Fin n)
                    (@EconCSLib.Auction.PaperTheorem7OrderedRankedCanonicalTailComparisonPaymentCertificate.vcgOutcome n
                      model)
                    i))
              (∀ (other : EconCSLib.Auction.PositionOutcome.{0, 0} (Fin n) (Fin n)),
                @EconCSLib.Auction.PositionOutcome.FeasibleAssignment.{0, 0} (Fin n) (Fin n) other →
                  (@EconCSLib.Auction.PositionOutcome.IndividuallyRational.{0, 0} (Fin n) (Fin n)
                      (@EconCSLib.Auction.paper_theorem7_ranked_environment n
                        (@EconCSLib.Auction.PaperTheorem7OrderedRankedCanonicalTailComparisonPaymentCertificate.clickThroughRate
                          n model))
                      other fun (i : Fin n) =>
                      @EconCSLib.Auction.PaperTheorem7OrderedRankedCanonicalTailComparisonPaymentCertificate.value n
                        model (@Fin.val n i)) →
                    (@EconCSLib.Auction.PositionOutcome.SlotEnvyFree.{0, 0} (Fin n) (Fin n)
                        (@EconCSLib.Auction.paper_theorem7_ranked_environment n
                          (@EconCSLib.Auction.PaperTheorem7OrderedRankedCanonicalTailComparisonPaymentCertificate.clickThroughRate
                            n model))
                        other fun (i : Fin n) =>
                        @EconCSLib.Auction.PaperTheorem7OrderedRankedCanonicalTailComparisonPaymentCertificate.value n
                          model (@Fin.val n i)) →
                      (∀ (i : Fin n),
                          @Eq.{1} (Option.{0} (Fin n))
                            (@EconCSLib.Auction.PositionOutcome.slotOf.{0, 0} (Fin n) (Fin n) O i)
                            (@EconCSLib.Auction.PositionOutcome.slotOf.{0, 0} (Fin n) (Fin n) other i)) →
                        @EconCSLib.Auction.paper_position_no_positive_transfers.{0, 0} (Fin n) (Fin n) other →
                          @LE.le.{0} Real Real.instLE
                            (@EconCSLib.Auction.PositionOutcome.revenue.{0, 0} (Fin n) (Fin n) (Fin.fintype n)
                              (@EconCSLib.Auction.paper_theorem7_ranked_environment n
                                (@EconCSLib.Auction.PaperTheorem7OrderedRankedCanonicalTailComparisonPaymentCertificate.clickThroughRate
                                  n model))
                              O)
                            (@EconCSLib.Auction.PositionOutcome.revenue.{0, 0} (Fin n) (Fin n) (Fin.fintype n)
                              (@EconCSLib.Auction.paper_theorem7_ranked_environment n
                                (@EconCSLib.Auction.PaperTheorem7OrderedRankedCanonicalTailComparisonPaymentCertificate.clickThroughRate
                                  n model))
                              other)))))) := sorry

end EOS07GSP.PaperInterface
