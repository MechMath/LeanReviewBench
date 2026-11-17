import Mathlib
import dep.EconCSLib.Foundations.Probability.Gaussian
import dep.EconCSLib.Foundations.Probability.GaussianMathlib
import dep.LG21TestOptionalPolicies.MainTheorems

namespace LG21TestOptionalPolicies

noncomputable section

open EconCSLib

open EconCSLib.Probability

abbrev paperSchoolInformationSet (Base Test : Type*) :=
  LG21SchoolInformationSet Base Test

abbrev paperSchoolInformationSetFromAccessAction
    {Base Test : Type*}
    (observesAccess : Bool) (base : Base) (test : Test)
    (action : LG21AccessAction) :
    paperSchoolInformationSet Base Test :=
  LG21SchoolInformationSet.fromAccessAction observesAccess base test action

abbrev paperBaseMixedGaussianPosteriorLawSurface
    {Feature Base : Type*} [Fintype Feature] [DecidableEq Feature]
    (skillGivenBase : Base → PMF ℝ) (baseProfile : PMF Base)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (scoreLaw : Base → GaussianScaleLaw)
    (noAccessEstimate : Base → ℝ) :
    LG21SourceLawPolicySurface ℝ Base ℝ
      (LG21SkillBaseMixtureEstimateLaw ℝ Base) :=
  lg21BaseMixedGaussianPosteriorLawSurface
    skillGivenBase baseProfile M theta k scoreLaw noAccessEstimate

end

end LG21TestOptionalPolicies
