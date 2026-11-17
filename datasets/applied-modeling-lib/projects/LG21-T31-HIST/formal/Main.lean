import Mathlib
import dep.EconCSLib.Foundations.Probability.Gaussian
import dep.EconCSLib.Foundations.Probability.GaussianMathlib
import dep.LG21TestOptionalPolicies.MainTheorems
import dep.LG21TestOptionalPolicies.ProofInterface

namespace LG21TestOptionalPolicies

namespace PaperInterface

abbrev theorem3_1_optional_reporting.{u_1, u_2, u_3, u_4, u_5, u_6} : ∀ {Feature : Type u_1} {Base : Type u_2} {Equilibrium : Type u_3} [inst : Fintype.{u_1} Feature]
  [inst_1 : DecidableEq.{u_1 + 1} Feature] [Nonempty.{u_2 + 1} Base]
  (skillGivenBase : Equilibrium → Base → PMF.{0} Real) (baseProfile : Equilibrium → PMF.{u_2} Base)
  (M : Base → @EconCSLib.Probability.GaussianOffsetSignalFamily.{u_1} Feature inst) (theta : Base → Feature → Real)
  (k : Feature) (accessFraction baseOnlyEstimate : Equilibrium → Base → Real)
  (scoreLaw : Equilibrium → Base → EconCSLib.Probability.GaussianScaleLaw)
  (hC_nonneg :
    ∀ (e : Equilibrium) (base : Base),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (accessFraction e base))
  (hC_lt_one :
    ∀ (e : Equilibrium) (base : Base),
      @LT.lt.{0} Real Real.instLT (accessFraction e base)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
  And
    (∀ (base : Base) (test : Real) (action : LG21TestOptionalPolicies.LG21AccessAction),
      @Eq.{1} (Option.{0} LG21TestOptionalPolicies.LG21AccessStatus)
        (@LG21TestOptionalPolicies.LG21SchoolInformationSet.accessStatus.{u_2, 0} Base Real
          (@LG21TestOptionalPolicies.paperSchoolInformationSetFromAccessAction.{u_2, 0} Base Real Bool.false base test
            action))
        (@Option.none.{0} LG21TestOptionalPolicies.LG21AccessStatus))
    (∀ (e : Equilibrium),
      @Exists.{u_2 + 1} (LG21TestOptionalPolicies.LG21OptionalReportingStrategicWithholdingSourceWitness.{u_2} Base)
        fun (W : LG21TestOptionalPolicies.LG21OptionalReportingStrategicWithholdingSourceWitness.{u_2} Base) =>
        And
          (∀ (base : Base) (skill : Real),
            @LG21TestOptionalPolicies.LG21OptionalReportingStrategicWithholdingSourceWitness.takes.{u_2} Base W base
              skill)
          (And
            (@Exists.{u_2 + 1} Base fun (base : Base) =>
              @Exists.{1} Real fun (score : Real) =>
                Not
                  (@LG21TestOptionalPolicies.LG21OptionalReportingStrategicWithholdingSourceWitness.reports.{u_2} Base W
                    base score))
            (And
              (∀ (base : Base),
                @Exists.{1} Real fun (cutoff : Real) =>
                  ∀ (score : Real),
                    Iff
                      (@LG21TestOptionalPolicies.LG21OptionalReportingStrategicWithholdingSourceWitness.reports.{u_2}
                        Base W base score)
                      (@LE.le.{0} Real Real.instLE cutoff score))
              (And
                (Not
                  (@LG21TestOptionalPolicies.lg21SourceLawLatentSkillFair.{0, u_2, 0, u_2, u_4} Real Base Real
                    (LG21TestOptionalPolicies.LG21SkillBaseMixtureEstimateLaw.{0, u_2} Real Base)
                    (@LG21TestOptionalPolicies.paperBaseMixedGaussianPosteriorLawSurface.{u_1, u_2, u_4} Feature Base
                      inst inst_1 (skillGivenBase e) (baseProfile e) M theta k (scoreLaw e) (baseOnlyEstimate e))))
                (And
                  (Not
                    (@LG21TestOptionalPolicies.lg21SourceLawObservablyFair.{0, u_2, 0, u_2, u_5} Real Base Real
                      (LG21TestOptionalPolicies.LG21SkillBaseMixtureEstimateLaw.{0, u_2} Real Base)
                      (@LG21TestOptionalPolicies.paperBaseMixedGaussianPosteriorLawSurface.{u_1, u_2, u_5} Feature Base
                        inst inst_1 (skillGivenBase e) (baseProfile e) M theta k (scoreLaw e) (baseOnlyEstimate e))))
                  (Not
                    (@LG21TestOptionalPolicies.lg21SourceLawDemographicallyFair.{0, u_2, 0, u_2, u_6} Real Base Real
                      (LG21TestOptionalPolicies.LG21SkillBaseMixtureEstimateLaw.{0, u_2} Real Base)
                      (@LG21TestOptionalPolicies.paperBaseMixedGaussianPosteriorLawSurface.{u_1, u_2, u_6} Feature Base
                        inst inst_1 (skillGivenBase e) (baseProfile e) M theta k (scoreLaw e)
                        (baseOnlyEstimate e))))))))) := sorry

end PaperInterface

end LG21TestOptionalPolicies
