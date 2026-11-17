import Mathlib
import dep.EconCSLib.Foundations.Probability.Gaussian
import dep.EconCSLib.Foundations.Probability.GaussianMathlib

open EconCSLib

open EconCSLib.Probability

open scoped ENNReal

namespace LG21TestOptionalPolicies

noncomputable section

inductive LG21AccessStatus where
  | noAccess
  | access
deriving DecidableEq

namespace LG21AccessStatus

end LG21AccessStatus

structure LG21SchoolInformationSet (Base Test : Type*) where
  accessStatus : Option LG21AccessStatus
  baseProfile : Base
  reportsScore : Bool
  reportedTestScore : Option Test

def lg21GaussianTestScoreLaw (skill scale : ℝ) (hscale : 0 < scale) :
    GaussianScaleLaw where
  mean := skill
  scale := scale
  scale_pos := hscale

def lg21OneTestPosteriorScoreLaw
    (intercept slope : ℝ) (hslope : 0 < slope)
    (skill testScale : ℝ) (htestScale : 0 < testScale) :
    GaussianScaleLaw :=
  (lg21GaussianTestScoreLaw skill testScale htestScale).affineImage
    intercept slope hslope

inductive LG21SkillBaseMixtureEstimateLaw (Skill Base : Type*) where
  | point : ℝ → LG21SkillBaseMixtureEstimateLaw Skill Base
  | gaussian : GaussianScaleLaw → LG21SkillBaseMixtureEstimateLaw Skill Base
  | skillGaussianMixture :
      PMF Skill → (Skill → GaussianScaleLaw) →
        LG21SkillBaseMixtureEstimateLaw Skill Base
  | baseSkillGaussianMixture :
      PMF Base → (Base → PMF Skill) → (Base → Skill → GaussianScaleLaw) →
        LG21SkillBaseMixtureEstimateLaw Skill Base
  | basePointMixture :
      PMF Base → (Base → ℝ) → LG21SkillBaseMixtureEstimateLaw Skill Base

namespace LG21SkillBaseMixtureEstimateLaw

end LG21SkillBaseMixtureEstimateLaw

namespace LG21GaussianMixtureLaw

end LG21GaussianMixtureLaw

structure LG21AccessAction where
  takesTest : Bool
  reportsScore : Bool
deriving DecidableEq, Repr

namespace LG21AccessAction

end LG21AccessAction

namespace LG21SchoolInformationSet

def fromAccessAction
    {Base Test : Type*}
    (observesAccess : Bool) (base : Base) (test : Test)
    (action : LG21AccessAction) : LG21SchoolInformationSet Base Test where
  accessStatus :=
    if observesAccess then some LG21AccessStatus.access else none
  baseProfile := base
  reportsScore := action.reportsScore
  reportedTestScore := if action.reportsScore then some test else none

end LG21SchoolInformationSet

namespace LG21RequirementPolicy

end LG21RequirementPolicy

namespace LG21AccessStudentInfo

end LG21AccessStudentInfo

structure LG21SourceLawPolicySurface
    (Skill Base Test Law : Type*) where
  Equilibrium : Type*
  latentAccessLaw : Equilibrium → Skill → Base → Law
  latentNoAccessLaw : Equilibrium → Skill → Base → Law
  observableAccessLaw : Equilibrium → Base → Law
  observableNoAccessLaw : Equilibrium → Base → Law
  demographicAccessLaw : Equilibrium → Law
  demographicNoAccessLaw : Equilibrium → Law
  baseOnlyLaw : Equilibrium → Base → Law
  fullFeatureLaw : Equilibrium → Base → Test → Law

def lg21SourceLawLatentSkillFair
    {Skill Base Test Law : Type*}
    (S : LG21SourceLawPolicySurface Skill Base Test Law) : Prop :=
  ∀ e q base, S.latentAccessLaw e q base =
    S.latentNoAccessLaw e q base

def lg21SourceLawObservablyFair
    {Skill Base Test Law : Type*}
    (S : LG21SourceLawPolicySurface Skill Base Test Law) : Prop :=
  ∀ e base, S.observableAccessLaw e base =
    S.observableNoAccessLaw e base

def lg21SourceLawDemographicallyFair
    {Skill Base Test Law : Type*}
    (S : LG21SourceLawPolicySurface Skill Base Test Law) : Prop :=
  ∀ e, S.demographicAccessLaw e = S.demographicNoAccessLaw e

structure LG21OptionalReportingStrategicWithholdingSourceWitness
    (Base : Type*) where
  reports : Base → ℝ → Prop
  takes : Base → ℝ → Prop
  all_take : ∀ base skill, takes base skill
  some_access_students_do_not_report : ∃ base score, ¬ reports base score
  reporting_threshold :
    ∀ base, ∃ cutoff : ℝ, ∀ score : ℝ, reports base score ↔ cutoff ≤ score

def lg21BaseMixedOneTestPosteriorLawSurface
    {Base : Type*}
    (skillGivenBase : Base → PMF ℝ) (baseProfile : PMF Base)
    (intercept slope testScale noAccessEstimate : Base → ℝ)
    (hslope : ∀ base : Base, 0 < slope base)
    (htestScale : ∀ base : Base, 0 < testScale base) :
    LG21SourceLawPolicySurface ℝ Base ℝ
      (LG21SkillBaseMixtureEstimateLaw ℝ Base) where
  Equilibrium := PUnit
  latentAccessLaw := fun _ skill base =>
    LG21SkillBaseMixtureEstimateLaw.gaussian
      (lg21OneTestPosteriorScoreLaw
        (intercept base) (slope base) (hslope base)
        skill (testScale base) (htestScale base))
  latentNoAccessLaw := fun _ _ base =>
    LG21SkillBaseMixtureEstimateLaw.point (noAccessEstimate base)
  observableAccessLaw := fun _ base =>
    LG21SkillBaseMixtureEstimateLaw.skillGaussianMixture
      (skillGivenBase base)
      (fun skill =>
        lg21OneTestPosteriorScoreLaw
          (intercept base) (slope base) (hslope base)
          skill (testScale base) (htestScale base))
  observableNoAccessLaw := fun _ base =>
    LG21SkillBaseMixtureEstimateLaw.point (noAccessEstimate base)
  demographicAccessLaw := fun _ =>
    LG21SkillBaseMixtureEstimateLaw.baseSkillGaussianMixture
      baseProfile skillGivenBase
      (fun base skill =>
        lg21OneTestPosteriorScoreLaw
          (intercept base) (slope base) (hslope base)
          skill (testScale base) (htestScale base))
  demographicNoAccessLaw := fun _ =>
    LG21SkillBaseMixtureEstimateLaw.basePointMixture
      baseProfile noAccessEstimate
  baseOnlyLaw := fun _ base =>
    LG21SkillBaseMixtureEstimateLaw.point (noAccessEstimate base)
  fullFeatureLaw := fun _ base test =>
    LG21SkillBaseMixtureEstimateLaw.gaussian
      (lg21OneTestPosteriorScoreLaw
        (intercept base) (slope base) (hslope base)
        test (testScale base) (htestScale base))

def lg21BaseMixedGaussianPosteriorLawSurface
    {Feature Base : Type*} [Fintype Feature] [DecidableEq Feature]
    (skillGivenBase : Base → PMF ℝ) (baseProfile : PMF Base)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (scoreLaw : Base → GaussianScaleLaw)
    (noAccessEstimate : Base → ℝ) :
    LG21SourceLawPolicySurface ℝ Base ℝ
      (LG21SkillBaseMixtureEstimateLaw ℝ Base) :=
  lg21BaseMixedOneTestPosteriorLawSurface
    skillGivenBase baseProfile
    (fun base => (M base).posteriorMean (Function.update (theta base) k 0))
    (fun base => (M base).centeredFamily.signalWeight k)
    (fun base => (scoreLaw base).scale)
    noAccessEstimate
    (fun base => (M base).centeredFamily.signalWeight_pos k)
    (fun base => (scoreLaw base).scale_pos)

end

end LG21TestOptionalPolicies
