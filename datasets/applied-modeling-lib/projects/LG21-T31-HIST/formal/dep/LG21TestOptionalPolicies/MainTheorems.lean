import Mathlib

import dep.EconCSLib.Foundations.Probability.Gaussian
import dep.EconCSLib.Foundations.Probability.GaussianMathlib
import dep.EconCSLib.Foundations.Math.AffineThreshold
import dep.EconCSLib.Foundations.Math.ThresholdCharacterization
open EconCSLib
open EconCSLib.Probability
open scoped ENNReal

/-!
# Paper-Facing Theorems: Test-optional Policies and Informational Gaps

This file currently exposes the finite admissions-accounting layer used as
support for the future source-faithful formalization of
*Test-optional Policies: Overcoming Strategic Behavior and Informational Gaps*.

## Main declarations

- `LG21Model`, `LG21AccessStatus`, `LG21SchoolInformationSet`, and
  `LG21RequirementPolicy`: source model primitives for access status,
  information sets, and test-taking/reporting requirements.
- `lg21TwoSignalAdmissionsModel`: adapter to the reusable two-signal
  admissions comparison interface.
- `lg21BaseModel`, `lg21TestModel`: wrappers into the reusable
  `AdmissionsModel`.
- `LG21ResamplingExperiment`: finite conditional-kernel interface for the
  re-sampling policy in Definition 6.
- `LG21EquilibriumData`, `lg21Equilibrium`, `LG21SourcePolicySurface`:
  source-facing equilibrium and fairness surfaces for the strategic parts of
  the paper.
- `paper_lemma4_1_observed_access_chosen_actions_of_fully_specified_source_models`:
  the closed observed-access source-model endpoint for Lemma 4.1.
- `LG21StrategicWithholdingSourceWitness`: the current bridge target for
  Theorem 3.1's threshold and unfairness conclusions.
- `paper_theorem4_4_resampling_policy_observably_fair`,
  `paper_theorem4_4_resampling_policy_demographically_fair`: finite
  distributional core of Theorem 4.4.
- `lg21_base_exp_decompose`, `lg21_test_exp_decompose`: finite expectation
  decompositions for selected and unselected applicants.
-/

namespace LG21TestOptionalPolicies

noncomputable section

/-!
Core abstraction for a test-optional paper-facing model: students have a latent
quality and two signal channels (base profile and optional test outcome).  Both
use the same prior to enable direct comparison.
-/
inductive LG21AccessStatus where
  | noAccess
  | access
deriving DecidableEq

namespace LG21AccessStatus

/- Boolean form of the source indicator `Z`. -/
end LG21AccessStatus

/-
The school's information set in Sections 3--4.  `accessStatus = none` is the
Section 3 case where the school does not observe `Z`; `some z` is the Section 4
case where `Z` is included in the information set.  The test score is present
exactly when the student reports it.
-/
structure LG21SchoolInformationSet (Base Test : Type*) where
  accessStatus : Option LG21AccessStatus
  baseProfile : Base
  reportsScore : Bool
  reportedTestScore : Option Test

theorem paper_bayesian_optimal_estimator_strictMono_feature
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature) :
    StrictMono (fun value : ℝ =>
      M.posteriorMean (Function.update theta k value)) :=
  M.posteriorMean_update_strictMono theta k

/-
Threshold support for reporting/taking decisions: a positive-slope affine
Bayesian estimate clears a reporting threshold exactly above its cutoff.
-/
theorem paper_gaussian_posteriorMean_update_continuous
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature) :
    Continuous (fun value : ℝ =>
      M.posteriorMean (Function.update theta k value)) := by
  have hfun :
      (fun value : ℝ =>
          M.posteriorMean (Function.update theta k value)) =
        fun value : ℝ =>
          M.posteriorMean (Function.update theta k 0) +
            M.centeredFamily.signalWeight k * value := by
    funext value
    exact M.posteriorMean_update_eq_base_add_weight_mul theta k value
  rw [hfun]
  exact continuous_const.add (continuous_const.mul continuous_id)

/-
Gaussian posterior-score support for Lemma 4.1: because the reported score
enters the Bayesian posterior estimate with positive slope, for every cutoff
and no-report estimate there is a sufficiently low reported score whose
posterior estimate is below the no-report estimate.
-/
theorem paper_gaussian_posteriorMean_update_exists_above_after
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (lower level : ℝ) :
    ∃ score : ℝ,
      lower < score ∧
        level < M.posteriorMean (Function.update theta k score) := by
  let base0 : ℝ := M.posteriorMean (Function.update theta k 0)
  let weight : ℝ := M.centeredFamily.signalWeight k
  have hweight : 0 < weight := by
    simpa [weight] using M.centeredFamily.signalWeight_pos k
  rcases exists_lt_affine_after lower base0 level hweight with
    ⟨score, hlower, hscore⟩
  refine ⟨score, hlower, ?_⟩
  calc
    level < base0 + weight * score := hscore
    _ = M.posteriorMean (Function.update theta k score) := by
      simpa [base0, weight] using
        (M.posteriorMean_update_eq_base_add_weight_mul theta k score).symm

/-
Lemma 4.1 Gaussian reporting core: a nontrivial observed-access reporting
cutoff is unstable whenever the no-report posterior estimate is strictly
between the reported-score estimate at a lower score and the estimate at the
cutoff.  The conclusion exhibits the paper's `θ̃_K` and the interval of
withheld scores that weakly benefit from reporting.
-/
theorem paper_theorem3_1_standard_lower_tail_posterior_update_continuous
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (scoreLaw : GaussianScaleLaw) :
    Continuous (fun cutoff : ℝ =>
      M.posteriorMean
        (Function.update theta k
          (standardGaussianLowerTailMean scoreLaw cutoff))) :=
  (paper_gaussian_posteriorMean_update_continuous M theta k).comp
    (standardGaussianLowerTailMean_continuous scoreLaw)

/-
Source-form no-report estimate for the unobserved-access optional-reporting
proof.  Among students with no reported score, a `(1 - C)` no-access mass with
base-only estimate is pooled with a `C * F(cutoff)` access mass whose test
score is below the reporting cutoff.
-/
def lg21OptionalNoReportMixtureEstimate
    (accessFraction baseOnlyEstimate : ℝ)
    (scoreLaw : GaussianScaleLaw)
    (accessLowerTailEstimate : ℝ → ℝ) (cutoff : ℝ) : ℝ :=
  ((1 - accessFraction) * baseOnlyEstimate +
      accessFraction * standardGaussianCDFAPI.normalCDF scoreLaw cutoff *
        accessLowerTailEstimate cutoff) /
    ((1 - accessFraction) +
      accessFraction * standardGaussianCDFAPI.normalCDF scoreLaw cutoff)

theorem lg21OptionalNoReportMixtureEstimate_denominator_pos
    {accessFraction : ℝ} (hC_nonneg : 0 ≤ accessFraction)
    (hC_lt_one : accessFraction < 1)
    (scoreLaw : GaussianScaleLaw) (cutoff : ℝ) :
    0 <
      (1 - accessFraction) +
        accessFraction * standardGaussianCDFAPI.normalCDF scoreLaw cutoff := by
  have hbase : 0 < 1 - accessFraction := by
    linarith
  have haccess :
      0 ≤ accessFraction * standardGaussianCDFAPI.normalCDF scoreLaw cutoff :=
    mul_nonneg hC_nonneg
      (standardGaussianCDFAPI.normalCDF_nonneg scoreLaw cutoff)
  linarith

/-
If both source components in the unobserved-access no-action pool are strictly
above a finite target, then the pooled estimate is above that target.
-/
theorem lt_lg21OptionalNoReportMixtureEstimate_of_weighted_gap_pos
    {accessFraction : ℝ} (hC_nonneg : 0 ≤ accessFraction)
    (hC_lt_one : accessFraction < 1)
    {baseOnlyEstimate target cutoff : ℝ}
    {scoreLaw : GaussianScaleLaw}
    {accessLowerTailEstimate : ℝ → ℝ}
    (hgap :
      0 <
        (1 - accessFraction) * (baseOnlyEstimate - target) +
          (accessFraction * standardGaussianCDFAPI.normalCDF scoreLaw cutoff) *
            (accessLowerTailEstimate cutoff - target)) :
    target <
      lg21OptionalNoReportMixtureEstimate
        accessFraction baseOnlyEstimate scoreLaw accessLowerTailEstimate cutoff := by
  let F : ℝ := standardGaussianCDFAPI.normalCDF scoreLaw cutoff
  let w0 : ℝ := 1 - accessFraction
  let w1 : ℝ := accessFraction * F
  have hdenom_pos : 0 < w0 + w1 := by
    dsimp [w0, w1, F]
    exact lg21OptionalNoReportMixtureEstimate_denominator_pos
      hC_nonneg hC_lt_one scoreLaw cutoff
  have hgap' :
      0 < w0 * (baseOnlyEstimate - target) +
          w1 * (accessLowerTailEstimate cutoff - target) := by
    simpa [w0, w1, F] using hgap
  have hnum :
      (w0 + w1) * target <
        w0 * baseOnlyEstimate + w1 * accessLowerTailEstimate cutoff := by
    nlinarith
  calc
    target = ((w0 + w1) * target) / (w0 + w1) := by
      rw [mul_div_cancel_left₀ target (ne_of_gt hdenom_pos)]
    _ <
        (w0 * baseOnlyEstimate + w1 * accessLowerTailEstimate cutoff) /
          (w0 + w1) :=
      div_lt_div_of_pos_right hnum hdenom_pos
    _ =
        lg21OptionalNoReportMixtureEstimate
          accessFraction baseOnlyEstimate scoreLaw accessLowerTailEstimate cutoff := by
      simp [lg21OptionalNoReportMixtureEstimate, w0, w1, F, mul_assoc]

/-
If both source components in the unobserved-access no-action pool are strictly
below a finite target, then the pooled estimate is below that target.
-/
theorem lg21OptionalNoReportMixtureEstimate_lt_of_components_lt
    {accessFraction : ℝ} (hC_nonneg : 0 ≤ accessFraction)
    (hC_lt_one : accessFraction < 1)
    {baseOnlyEstimate target cutoff : ℝ}
    {scoreLaw : GaussianScaleLaw}
    {accessLowerTailEstimate : ℝ → ℝ}
    (hbase : baseOnlyEstimate < target)
    (haccess : accessLowerTailEstimate cutoff < target) :
    lg21OptionalNoReportMixtureEstimate
        accessFraction baseOnlyEstimate scoreLaw accessLowerTailEstimate cutoff <
      target := by
  let F : ℝ := standardGaussianCDFAPI.normalCDF scoreLaw cutoff
  let w0 : ℝ := 1 - accessFraction
  let w1 : ℝ := accessFraction * F
  have hw0_pos : 0 < w0 := by
    dsimp [w0]
    linarith
  have hw1_nonneg : 0 ≤ w1 := by
    dsimp [w1, F]
    exact mul_nonneg hC_nonneg
      (standardGaussianCDFAPI.normalCDF_nonneg scoreLaw cutoff)
  have hdenom_pos : 0 < w0 + w1 := by
    linarith
  have hnum :
      w0 * baseOnlyEstimate + w1 * accessLowerTailEstimate cutoff <
        (w0 + w1) * target := by
    have h0 : w0 * baseOnlyEstimate < w0 * target :=
      mul_lt_mul_of_pos_left hbase hw0_pos
    have h1 : w1 * accessLowerTailEstimate cutoff ≤ w1 * target :=
      mul_le_mul_of_nonneg_left haccess.le hw1_nonneg
    nlinarith
  calc
    lg21OptionalNoReportMixtureEstimate
        accessFraction baseOnlyEstimate scoreLaw accessLowerTailEstimate cutoff =
        (w0 * baseOnlyEstimate + w1 * accessLowerTailEstimate cutoff) /
          (w0 + w1) := by
      simp [lg21OptionalNoReportMixtureEstimate, w0, w1, F, mul_assoc]
    _ < ((w0 + w1) * target) / (w0 + w1) :=
      div_lt_div_of_pos_right hnum hdenom_pos
    _ = target := by
      rw [mul_div_cancel_left₀ target (ne_of_gt hdenom_pos)]

/-
Exact finite-endpoint algebra for the unobserved-access no-action pool: if the
weighted component gap above the target is negative, then the pooled estimate
is below the target.
-/
theorem lg21OptionalNoReportMixtureEstimate_continuous
    {accessFraction : ℝ} (hC_nonneg : 0 ≤ accessFraction)
    (hC_lt_one : accessFraction < 1)
    (baseOnlyEstimate : ℝ) (scoreLaw : GaussianScaleLaw)
    {accessLowerTailEstimate : ℝ → ℝ}
    (hcontAccess : Continuous accessLowerTailEstimate) :
    Continuous (fun cutoff : ℝ =>
      lg21OptionalNoReportMixtureEstimate
        accessFraction baseOnlyEstimate scoreLaw accessLowerTailEstimate cutoff) := by
  have hcdf :
      Continuous (fun cutoff : ℝ =>
        standardGaussianCDFAPI.normalCDF scoreLaw cutoff) :=
    standardGaussianCDFAPI.normalCDF_continuous scoreLaw
  have hdenom :
      ∀ cutoff : ℝ,
        ((1 - accessFraction) +
            accessFraction * standardGaussianCDFAPI.normalCDF scoreLaw cutoff) ≠
          0 := by
    intro cutoff
    exact ne_of_gt
      (lg21OptionalNoReportMixtureEstimate_denominator_pos
        hC_nonneg hC_lt_one scoreLaw cutoff)
  dsimp [lg21OptionalNoReportMixtureEstimate]
  exact
    (continuous_const.add
        ((continuous_const.mul hcdf).mul hcontAccess)).div
      (continuous_const.add (continuous_const.mul hcdf)) hdenom

/-
Theorem 3.1 optional-reporting source formula support specialized to the
Gaussian lower-tail posterior estimate used for access students below the
reporting cutoff.
-/
theorem paper_theorem3_1_optional_no_report_mixture_standard_lower_tail_continuous
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {accessFraction : ℝ} (hC_nonneg : 0 ≤ accessFraction)
    (hC_lt_one : accessFraction < 1)
    (baseOnlyEstimate : ℝ)
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (scoreLaw : GaussianScaleLaw) :
    Continuous (fun cutoff : ℝ =>
      lg21OptionalNoReportMixtureEstimate
        accessFraction baseOnlyEstimate scoreLaw
        (fun cutoff : ℝ =>
          M.posteriorMean
            (Function.update theta k
              (standardGaussianLowerTailMean scoreLaw cutoff)))
        cutoff) :=
  lg21OptionalNoReportMixtureEstimate_continuous
    hC_nonneg hC_lt_one baseOnlyEstimate scoreLaw
    (paper_theorem3_1_standard_lower_tail_posterior_update_continuous
      M theta k scoreLaw)

/-
Theorem 3.1 report-required source formula support: the pooled no-take estimate
is continuous when the access lower-tail component is a positive-slope affine
function of the Gaussian lower-tail skill mean.
-/
theorem paper_theorem3_1_standard_lower_tail_posterior_update_lt_reported
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (scoreLaw : GaussianScaleLaw) (cutoff : ℝ) :
    M.posteriorMean
        (Function.update theta k
          (standardGaussianLowerTailMean scoreLaw cutoff)) <
      M.posteriorMean (Function.update theta k cutoff) := by
  exact
    (paper_bayesian_optimal_estimator_strictMono_feature M theta k)
      (standardGaussianLowerTailMean_lt_threshold scoreLaw cutoff)

/-
Theorem 3.1 lower-tail component comparison for report-required policies:
passing the lower-tail skill mean through a positive-slope affine estimate is
strictly below evaluating the affine estimate at the cutoff skill.
-/
theorem paper_theorem3_1_optional_no_report_mixture_high_endpoint_exists_after
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {accessFraction : ℝ} (hC_nonneg : 0 ≤ accessFraction)
    (hC_lt_one : accessFraction < 1)
    (baseOnlyEstimate : ℝ)
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (scoreLaw : GaussianScaleLaw) (low : ℝ) :
    ∃ high : ℝ,
      low < high ∧
        lg21OptionalNoReportMixtureEstimate
            accessFraction baseOnlyEstimate scoreLaw
            (fun cutoff : ℝ =>
              M.posteriorMean
                (Function.update theta k
                  (standardGaussianLowerTailMean scoreLaw cutoff)))
            high <
          M.posteriorMean (Function.update theta k high) := by
  rcases paper_gaussian_posteriorMean_update_exists_above_after
      M theta k low baseOnlyEstimate with
    ⟨high, hlow_high, hbase⟩
  refine ⟨high, hlow_high, ?_⟩
  exact
    lg21OptionalNoReportMixtureEstimate_lt_of_components_lt
      hC_nonneg hC_lt_one hbase
      (paper_theorem3_1_standard_lower_tail_posterior_update_lt_reported
        M theta k scoreLaw high)

/-
Theorem 3.1 report-required high endpoint for the paper's source mixture.  At
some finite high taking cutoff, the pooled no-take estimate lies below the
take/report payoff at the cutoff.
-/
theorem paper_theorem3_1_affine_lower_tail_mixture_low_endpoint_exists
    {accessFraction : ℝ} (hC_nonneg : 0 ≤ accessFraction)
    (hC_lt_one : accessFraction < 1)
    (baseOnlyEstimate intercept : ℝ) {slope : ℝ} (hslope : 0 < slope)
    (scoreLaw : GaussianScaleLaw) :
    ∃ low : ℝ,
      intercept + slope * low <
        lg21OptionalNoReportMixtureEstimate
          accessFraction baseOnlyEstimate scoreLaw
          (fun cutoff : ℝ =>
            intercept + slope * standardGaussianLowerTailMean scoreLaw cutoff)
          low := by
  have htail :
      Filter.Tendsto
        (fun cutoff : ℝ =>
          standardGaussianCDFAPI.normalCDF scoreLaw cutoff *
            (standardGaussianLowerTailMean scoreLaw cutoff - cutoff))
        Filter.atBot (nhds 0) := by
    simpa [StandardGaussianCDFAPI.normalCDF, standardGaussianCDFAPI] using
      standardGaussian_normalCDF_mul_lowerTailMean_sub_tendsto_atBot scoreLaw
  have haccess :
      Filter.Tendsto
        (fun cutoff : ℝ =>
          (accessFraction *
              standardGaussianCDFAPI.normalCDF scoreLaw cutoff) *
              ((intercept + slope *
                standardGaussianLowerTailMean scoreLaw cutoff) -
              (intercept + slope * cutoff)))
        Filter.atBot (nhds 0) := by
    have hconst :=
      (tendsto_const_nhds (x := accessFraction * slope)).mul htail
    have hconst_zero :
        Filter.Tendsto
          (fun cutoff : ℝ =>
            (accessFraction * slope) *
              (standardGaussianCDFAPI.normalCDF scoreLaw cutoff *
                (standardGaussianLowerTailMean scoreLaw cutoff - cutoff)))
          Filter.atBot (nhds 0) := by
      simpa using hconst
    refine hconst_zero.congr' ?_
    filter_upwards with cutoff
    ring
  have hbase :
      Filter.Tendsto
        (fun cutoff : ℝ =>
          (1 - accessFraction) *
            (baseOnlyEstimate - (intercept + slope * cutoff)))
        Filter.atBot Filter.atTop := by
    have hmass_pos : 0 < 1 - accessFraction := by
      linarith
    have hcoef_neg : -((1 - accessFraction) * slope) < 0 := by
      nlinarith
    have hlin :
        Filter.Tendsto
          (fun cutoff : ℝ =>
            -((1 - accessFraction) * slope) * cutoff +
              (1 - accessFraction) * (baseOnlyEstimate - intercept))
          Filter.atBot Filter.atTop :=
      (Filter.Tendsto.const_mul_atBot_of_neg hcoef_neg
        Filter.tendsto_id).atTop_add tendsto_const_nhds
    refine hlin.congr' ?_
    filter_upwards with cutoff
    ring
  have hgap_tendsto :
      Filter.Tendsto
        (fun cutoff : ℝ =>
          (1 - accessFraction) *
              (baseOnlyEstimate - (intercept + slope * cutoff)) +
            (accessFraction *
                standardGaussianCDFAPI.normalCDF scoreLaw cutoff) *
              ((intercept + slope *
                  standardGaussianLowerTailMean scoreLaw cutoff) -
                (intercept + slope * cutoff)))
        Filter.atBot Filter.atTop :=
    hbase.atTop_add haccess
  have hgap_event :
      ∀ᶠ cutoff in Filter.atBot,
        0 <
          (1 - accessFraction) *
              (baseOnlyEstimate - (intercept + slope * cutoff)) +
            (accessFraction *
                standardGaussianCDFAPI.normalCDF scoreLaw cutoff) *
              ((intercept + slope *
                  standardGaussianLowerTailMean scoreLaw cutoff) -
                (intercept + slope * cutoff)) :=
    hgap_tendsto.eventually (Filter.eventually_gt_atTop (0 : ℝ))
  rcases hgap_event.exists with ⟨low, hgap⟩
  refine ⟨low, ?_⟩
  exact
    lt_lg21OptionalNoReportMixtureEstimate_of_weighted_gap_pos
      hC_nonneg hC_lt_one hgap

/-
Theorem 3.1 optional-reporting low endpoint for the paper's Gaussian posterior
no-report mixture.
-/
theorem paper_theorem3_1_optional_no_report_mixture_low_endpoint_exists
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {accessFraction : ℝ} (hC_nonneg : 0 ≤ accessFraction)
    (hC_lt_one : accessFraction < 1)
    (baseOnlyEstimate : ℝ)
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (scoreLaw : GaussianScaleLaw) :
    ∃ low : ℝ,
      M.posteriorMean (Function.update theta k low) <
        lg21OptionalNoReportMixtureEstimate
          accessFraction baseOnlyEstimate scoreLaw
          (fun cutoff : ℝ =>
            M.posteriorMean
              (Function.update theta k
                (standardGaussianLowerTailMean scoreLaw cutoff)))
          low := by
  let intercept : ℝ := M.posteriorMean (Function.update theta k 0)
  let slope : ℝ := M.centeredFamily.signalWeight k
  have hslope : 0 < slope := by
    simpa [slope] using M.centeredFamily.signalWeight_pos k
  rcases
      paper_theorem3_1_affine_lower_tail_mixture_low_endpoint_exists
        hC_nonneg hC_lt_one baseOnlyEstimate intercept hslope scoreLaw with
    ⟨low, hlow⟩
  refine ⟨low, ?_⟩
  have hreported (score : ℝ) :
      M.posteriorMean (Function.update theta k score) =
        intercept + slope * score := by
    simpa [intercept, slope] using
      M.posteriorMean_update_eq_base_add_weight_mul theta k score
  convert hlow using 2
  · exact hreported low
  · ext cutoff
    exact hreported (standardGaussianLowerTailMean scoreLaw cutoff)

/-
Theorem 3.1 report-required low endpoint for the paper's affine no-take
mixture.
-/
def lg21GaussianTestScoreLaw (skill scale : ℝ) (hscale : 0 < scale) :
    GaussianScaleLaw where
  mean := skill
  scale := scale
  scale_pos := hscale

/-
Posterior-score law when all non-test features are fixed and the only random
input is one Gaussian test score.  `intercept + slope * testScore` is the
Bayesian posterior estimate as an affine function of the test score.
-/
def lg21OneTestPosteriorScoreLaw
    (intercept slope : ℝ) (hslope : 0 < slope)
    (skill testScale : ℝ) (htestScale : 0 < testScale) :
    GaussianScaleLaw :=
  (lg21GaussianTestScoreLaw skill testScale htestScale).affineImage
    intercept slope hslope



/-
Paper-local law type for Theorem 3.1's source-shaped continuous route.
It records the paper's conditional-on-skill Gaussian estimate laws, observable
laws obtained by mixing over latent skill at a fixed base profile, and
demographic laws obtained by mixing over base profiles.
-/
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

theorem gaussian_ne_point
    {Skill Base : Type*} (law : GaussianScaleLaw) (estimate : ℝ) :
    gaussian (Skill := Skill) (Base := Base) law ≠ point estimate := by
  intro h
  cases h

theorem skillGaussianMixture_ne_point
    {Skill Base : Type*} (skillLaw : PMF Skill)
    (lawBySkill : Skill → GaussianScaleLaw) (estimate : ℝ) :
    skillGaussianMixture (Skill := Skill) (Base := Base) skillLaw lawBySkill ≠
      point estimate := by
  intro h
  cases h

theorem baseSkillGaussianMixture_ne_basePointMixture
    {Skill Base : Type*} (baseProfile : PMF Base)
    (skillGivenBase : Base → PMF Skill)
    (lawByBaseSkill : Base → Skill → GaussianScaleLaw)
    (noAccessEstimate : Base → ℝ) :
    baseSkillGaussianMixture (Skill := Skill) (Base := Base)
        baseProfile skillGivenBase lawByBaseSkill ≠
      basePointMixture baseProfile noAccessEstimate := by
  intro h
  cases h

end LG21SkillBaseMixtureEstimateLaw

/-
Paper-local representation of Gaussian estimate laws and finite mixtures over
base profiles.  It is used for Proposition 4.3's demographic statement, where
the paper integrates base-conditioned estimate laws over the common
base-profile distribution.
-/
namespace LG21GaussianMixtureLaw

end LG21GaussianMixtureLaw

/-
Finite conditional-kernel form of the paper's Section 4.2 re-sampling policy.

The source proof of Theorem 4.4 only needs the distributional fact that, after
conditioning on the observed non-test profile, the imputed test score for a
student without access is sampled from the same conditional test-score law as a
student with access.  This paper-facing abbreviation points to the reusable
finite conditional-resampling interface in `EconCSLib`.
-/
structure LG21AccessAction where
  takesTest : Bool
  reportsScore : Bool
deriving DecidableEq, Repr

namespace LG21AccessAction

/- Source feasibility condition `Y ≥ X`: reporting requires taking the test. -/
end LG21AccessAction

namespace LG21SchoolInformationSet

/-
Information set induced by an access student's action.  This encodes the paper's
`I = ({θ_k}_{k<K}, X, θ_K 1_X)` in Section 3 and
`I = (Z, {θ_k}_{k<K}, X, θ_K 1_X)` in Section 4.
-/
def fromAccessAction
    {Base Test : Type*}
    (observesAccess : Bool) (base : Base) (test : Test)
    (action : LG21AccessAction) : LG21SchoolInformationSet Base Test where
  accessStatus :=
    if observesAccess then some LG21AccessStatus.access else none
  baseProfile := base
  reportsScore := action.reportsScore
  reportedTestScore := if action.reportsScore then some test else none

@[simp] theorem fromAccessAction_accessStatus_of_unobserved
    {Base Test : Type*} (base : Base) (test : Test)
    (action : LG21AccessAction) :
    (fromAccessAction false base test action).accessStatus = none := by
  rfl

end LG21SchoolInformationSet

/-
The three source requirement policies: no additional reporting requirement,
reporting required conditional on taking, and reporting required given access.
-/
namespace LG21RequirementPolicy

/- The requirement predicate on access-student actions. -/
end LG21RequirementPolicy

/-
Definition 1 student information for a student with test access.  The `test`
field is the realized optional test score that the reporting decision can use.
-/
namespace LG21AccessStudentInfo

/- The paper's chosen action `(Y(q, base), X(base, test))`. -/
end LG21AccessStudentInfo

/-
Estimate law conditional on an observed base profile after mixing over the
latent-skill distribution at that base profile.
-/
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

/- Definition 2: latent-skill fairness in every equilibrium. -/
def lg21SourceLawLatentSkillFair
    {Skill Base Test Law : Type*}
    (S : LG21SourceLawPolicySurface Skill Base Test Law) : Prop :=
  ∀ e q base, S.latentAccessLaw e q base =
    S.latentNoAccessLaw e q base

/- Definition 3 over arbitrary law objects. -/
def lg21SourceLawObservablyFair
    {Skill Base Test Law : Type*}
    (S : LG21SourceLawPolicySurface Skill Base Test Law) : Prop :=
  ∀ e base, S.observableAccessLaw e base =
    S.observableNoAccessLaw e base

/- Definition 4 over arbitrary law objects. -/
def lg21SourceLawDemographicallyFair
    {Skill Base Test Law : Type*}
    (S : LG21SourceLawPolicySurface Skill Base Test Law) : Prop :=
  ∀ e, S.demographicAccessLaw e = S.demographicNoAccessLaw e

/- Definition 5 over arbitrary law objects. -/
theorem lg21_not_lawLatentSkillFair_of_witness
    {Skill Base Test Law : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    (e : S.Equilibrium) (q : Skill) (base : Base)
    (hne : S.latentAccessLaw e q base ≠ S.latentNoAccessLaw e q base) :
    ¬ lg21SourceLawLatentSkillFair S := by
  intro hfair
  exact hne (hfair e q base)

/-
Proposition 4.2 four-group logical core: if no-access estimate laws are the
same for two latent skills at a fixed base profile, but access estimate laws
are different, then latent-skill fairness is impossible.
-/
theorem lg21_not_lawObservablyFair_of_witness
    {Skill Base Test Law : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    (e : S.Equilibrium) (base : Base)
    (hne : S.observableAccessLaw e base ≠ S.observableNoAccessLaw e base) :
    ¬ lg21SourceLawObservablyFair S := by
  intro hfair
  exact hne (hfair e base)

theorem lg21_not_lawDemographicallyFair_of_witness
    {Skill Base Test Law : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    (e : S.Equilibrium)
    (hne : S.demographicAccessLaw e ≠ S.demographicNoAccessLaw e) :
    ¬ lg21SourceLawDemographicallyFair S := by
  intro hfair
  exact hne (hfair e)

structure LG21OptionalReportingStrategicWithholdingSourceWitness
    (Base : Type*) where
  reports : Base → ℝ → Prop
  takes : Base → ℝ → Prop
  all_take : ∀ base skill, takes base skill
  some_access_students_do_not_report : ∃ base score, ¬ reports base score
  reporting_threshold :
    ∀ base, ∃ cutoff : ℝ, ∀ score : ℝ, reports base score ↔ cutoff ≤ score

/-
Concrete optional-reporting witness from base-indexed reporting cutoffs.  Taking
is identically true, and each reporting rule has a score one unit below its
cutoff that is withheld.
-/
theorem paper_theorem3_1_optional_reporting_threshold_cutoffs_of_base_crossings
    {Base : Type*} [Nonempty Base]
    (reportedEstimate noReportEstimateAtCutoff : Base → ℝ → ℝ)
    (low high : Base → ℝ)
    (hcontReported :
      ∀ base, ContinuousOn (reportedEstimate base)
        (Set.Icc (low base) (high base)))
    (hcontNoReport :
      ∀ base, ContinuousOn (noReportEstimateAtCutoff base)
        (Set.Icc (low base) (high base)))
    (hmonoReported : ∀ base, StrictMono (reportedEstimate base))
    (hlow_high : ∀ base, low base < high base)
    (hleft :
      ∀ base, reportedEstimate base (low base) <
        noReportEstimateAtCutoff base (low base))
    (hright :
      ∀ base, noReportEstimateAtCutoff base (high base) <
        reportedEstimate base (high base)) :
    ∃ reportCutoff : Base → ℝ,
      (∀ base, reportCutoff base ∈ Set.Ioo (low base) (high base)) ∧
        (∀ base,
          noReportEstimateAtCutoff base (reportCutoff base) =
            reportedEstimate base (reportCutoff base)) ∧
          (∀ base score,
            noReportEstimateAtCutoff base (reportCutoff base) ≤
                reportedEstimate base score ↔
              reportCutoff base ≤ score) ∧
            (∃ base score,
              ¬ noReportEstimateAtCutoff base (reportCutoff base) ≤
                  reportedEstimate base score) ∧
              (∀ base, ∃ cutoff : ℝ, ∀ score : ℝ,
                noReportEstimateAtCutoff base (reportCutoff base) ≤
                    reportedEstimate base score ↔
                  cutoff ≤ score) := by
  exact
    EconCSLib.exists_indexed_indifference_lower_cutoffs_of_continuous_strictMono_crossing
      reportedEstimate noReportEstimateAtCutoff low high
      hcontReported hcontNoReport hmonoReported hlow_high hleft hright

/-
Theorem 3.1 optional-reporting source witness from the paper's crossing
argument: continuity plus opposite endpoint comparisons produce threshold
reporting strategies; taking is identically true in the optional-reporting
case.
-/
theorem paper_theorem3_1_optional_reporting_source_witness_of_base_crossings
    {Base : Type*} [Nonempty Base]
    (reportedEstimate noReportEstimateAtCutoff : Base → ℝ → ℝ)
    (low high : Base → ℝ)
    (hcontReported :
      ∀ base, ContinuousOn (reportedEstimate base)
        (Set.Icc (low base) (high base)))
    (hcontNoReport :
      ∀ base, ContinuousOn (noReportEstimateAtCutoff base)
        (Set.Icc (low base) (high base)))
    (hmonoReported : ∀ base, StrictMono (reportedEstimate base))
    (hlow_high : ∀ base, low base < high base)
    (hleft :
      ∀ base, reportedEstimate base (low base) <
        noReportEstimateAtCutoff base (low base))
    (hright :
      ∀ base, noReportEstimateAtCutoff base (high base) <
        reportedEstimate base (high base)) :
    ∃ W : LG21OptionalReportingStrategicWithholdingSourceWitness Base,
      ∃ reportCutoff : Base → ℝ,
        (∀ base, reportCutoff base ∈ Set.Ioo (low base) (high base)) ∧
          (∀ base,
            noReportEstimateAtCutoff base (reportCutoff base) =
              reportedEstimate base (reportCutoff base)) ∧
            (∀ base score,
              W.reports base score ↔
                noReportEstimateAtCutoff base (reportCutoff base) ≤
                  reportedEstimate base score) ∧
              (∀ base skill, W.takes base skill) ∧
                (∀ base, ∃ cutoff : ℝ,
                  ∀ score : ℝ, W.reports base score ↔ cutoff ≤ score) := by
  rcases
    paper_theorem3_1_optional_reporting_threshold_cutoffs_of_base_crossings
      reportedEstimate noReportEstimateAtCutoff low high hcontReported
      hcontNoReport hmonoReported hlow_high hleft hright with
    ⟨reportCutoff, hmem, hindiff, hbest, hsome, hthreshold⟩
  let W : LG21OptionalReportingStrategicWithholdingSourceWitness Base :=
    { reports := fun base score =>
        noReportEstimateAtCutoff base (reportCutoff base) ≤
          reportedEstimate base score
      takes := fun _base _skill => True
      all_take := by
        intro _base _skill
        trivial
      some_access_students_do_not_report := hsome
      reporting_threshold := hthreshold }
  refine ⟨W, reportCutoff, hmem, hindiff, ?_, ?_, ?_⟩
  · intro _base _score
    rfl
  · intro _base _skill
    trivial
  · exact hthreshold

/-
Source-shaped witness for Theorem 3.1's report-required case.  The paper's
second bullet says taking-and-reporting is a finite lower cutoff in latent skill
at each base profile.
-/
theorem paper_theorem3_1_optional_reporting_gaussian_source_witness_of_crossings
    {Feature Base : Type*} [Fintype Feature] [DecidableEq Feature]
    [Nonempty Base]
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (noReportEstimateAtCutoff : Base → ℝ → ℝ)
    (low high : Base → ℝ)
    (hcontNoReport :
      ∀ base, ContinuousOn (noReportEstimateAtCutoff base)
        (Set.Icc (low base) (high base)))
    (hlow_high : ∀ base, low base < high base)
    (hleft :
      ∀ base,
        (M base).posteriorMean (Function.update (theta base) k (low base)) <
          noReportEstimateAtCutoff base (low base))
    (hright :
      ∀ base,
        noReportEstimateAtCutoff base (high base) <
          (M base).posteriorMean
            (Function.update (theta base) k (high base))) :
    ∃ W : LG21OptionalReportingStrategicWithholdingSourceWitness Base,
      ∃ reportCutoff : Base → ℝ,
        (∀ base, reportCutoff base ∈ Set.Ioo (low base) (high base)) ∧
          (∀ base,
            noReportEstimateAtCutoff base (reportCutoff base) =
              (M base).posteriorMean
                (Function.update (theta base) k (reportCutoff base))) ∧
            (∀ base score,
              W.reports base score ↔
                noReportEstimateAtCutoff base (reportCutoff base) ≤
                  (M base).posteriorMean
                    (Function.update (theta base) k score)) ∧
              (∀ base skill, W.takes base skill) ∧
                (∀ base, ∃ cutoff : ℝ,
                  ∀ score : ℝ, W.reports base score ↔ cutoff ≤ score) :=
  paper_theorem3_1_optional_reporting_source_witness_of_base_crossings
    (fun base score =>
      (M base).posteriorMean (Function.update (theta base) k score))
    noReportEstimateAtCutoff low high
    (fun base =>
      (paper_gaussian_posteriorMean_update_continuous
        (M base) (theta base) k).continuousOn)
    hcontNoReport
    (fun base =>
      paper_bayesian_optimal_estimator_strictMono_feature
        (M base) (theta base) k)
    hlow_high hleft hright

/-
Theorem 3.1 report-required affine crossing wrapper.  The expected estimate
from taking/reporting is affine and strictly increasing in latent skill; the
remaining hypotheses are the continuous no-take estimate and the source proof's
opposite endpoint comparisons.
-/
theorem paper_theorem3_1_optional_reporting_gaussian_source_witness_of_no_report_mixture_crossings
    {Feature Base : Type*} [Fintype Feature] [DecidableEq Feature]
    [Nonempty Base]
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (accessFraction baseOnlyEstimate : Base → ℝ)
    (scoreLaw : Base → GaussianScaleLaw)
    (low high : Base → ℝ)
    (hC_nonneg : ∀ base, 0 ≤ accessFraction base)
    (hC_lt_one : ∀ base, accessFraction base < 1)
    (hlow_high : ∀ base, low base < high base)
    (hleft :
      ∀ base,
        (M base).posteriorMean (Function.update (theta base) k (low base)) <
          lg21OptionalNoReportMixtureEstimate
            (accessFraction base) (baseOnlyEstimate base) (scoreLaw base)
            (fun cutoff : ℝ =>
              (M base).posteriorMean
                (Function.update (theta base) k
                  (standardGaussianLowerTailMean (scoreLaw base) cutoff)))
            (low base))
    (hright :
      ∀ base,
        lg21OptionalNoReportMixtureEstimate
            (accessFraction base) (baseOnlyEstimate base) (scoreLaw base)
            (fun cutoff : ℝ =>
              (M base).posteriorMean
                (Function.update (theta base) k
                  (standardGaussianLowerTailMean (scoreLaw base) cutoff)))
            (high base) <
          (M base).posteriorMean
            (Function.update (theta base) k (high base))) :
    ∃ W : LG21OptionalReportingStrategicWithholdingSourceWitness Base,
      ∃ reportCutoff : Base → ℝ,
        (∀ base, reportCutoff base ∈ Set.Ioo (low base) (high base)) ∧
          (∀ base,
            lg21OptionalNoReportMixtureEstimate
                (accessFraction base) (baseOnlyEstimate base) (scoreLaw base)
                (fun cutoff : ℝ =>
                  (M base).posteriorMean
                    (Function.update (theta base) k
                      (standardGaussianLowerTailMean (scoreLaw base) cutoff)))
                (reportCutoff base) =
              (M base).posteriorMean
                (Function.update (theta base) k (reportCutoff base))) ∧
            (∀ base score,
              W.reports base score ↔
                lg21OptionalNoReportMixtureEstimate
                    (accessFraction base) (baseOnlyEstimate base) (scoreLaw base)
                    (fun cutoff : ℝ =>
                      (M base).posteriorMean
                        (Function.update (theta base) k
                          (standardGaussianLowerTailMean (scoreLaw base) cutoff)))
                    (reportCutoff base) ≤
                  (M base).posteriorMean
                    (Function.update (theta base) k score)) ∧
              (∀ base skill, W.takes base skill) ∧
                (∀ base, ∃ cutoff : ℝ,
                  ∀ score : ℝ, W.reports base score ↔ cutoff ≤ score) :=
  paper_theorem3_1_optional_reporting_gaussian_source_witness_of_crossings
    M theta k
    (fun base cutoff =>
      lg21OptionalNoReportMixtureEstimate
        (accessFraction base) (baseOnlyEstimate base) (scoreLaw base)
        (fun cutoff : ℝ =>
          (M base).posteriorMean
            (Function.update (theta base) k
              (standardGaussianLowerTailMean (scoreLaw base) cutoff)))
        cutoff)
    low high
    (fun base =>
      (paper_theorem3_1_optional_no_report_mixture_standard_lower_tail_continuous
        (hC_nonneg base) (hC_lt_one base) (baseOnlyEstimate base)
        (M base) (theta base) k (scoreLaw base)).continuousOn)
    hlow_high hleft hright

/-
Theorem 3.1 report-required crossing wrapper specialized to the source no-take
mixture formula.  The Gaussian lower-tail/CDF algebra proves the continuity
premise; the remaining hypotheses are the finite endpoint comparisons used by
the paper's intermediate-value argument.
-/
theorem paper_theorem3_1_optional_reporting_gaussian_source_witness_of_no_report_mixture_low_endpoint
    {Feature Base : Type*} [Fintype Feature] [DecidableEq Feature]
    [Nonempty Base]
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (accessFraction baseOnlyEstimate : Base → ℝ)
    (scoreLaw : Base → GaussianScaleLaw)
    (low : Base → ℝ)
    (hC_nonneg : ∀ base, 0 ≤ accessFraction base)
    (hC_lt_one : ∀ base, accessFraction base < 1)
    (hleft :
      ∀ base,
        (M base).posteriorMean (Function.update (theta base) k (low base)) <
          lg21OptionalNoReportMixtureEstimate
            (accessFraction base) (baseOnlyEstimate base) (scoreLaw base)
            (fun cutoff : ℝ =>
              (M base).posteriorMean
                (Function.update (theta base) k
                  (standardGaussianLowerTailMean (scoreLaw base) cutoff)))
            (low base)) :
    ∃ W : LG21OptionalReportingStrategicWithholdingSourceWitness Base,
      ∃ reportCutoff : Base → ℝ,
        (∀ base, low base < reportCutoff base) ∧
          (∀ base,
            lg21OptionalNoReportMixtureEstimate
                (accessFraction base) (baseOnlyEstimate base) (scoreLaw base)
                (fun cutoff : ℝ =>
                  (M base).posteriorMean
                    (Function.update (theta base) k
                      (standardGaussianLowerTailMean (scoreLaw base) cutoff)))
                (reportCutoff base) =
              (M base).posteriorMean
                (Function.update (theta base) k (reportCutoff base))) ∧
            (∀ base score,
              W.reports base score ↔
                lg21OptionalNoReportMixtureEstimate
                    (accessFraction base) (baseOnlyEstimate base) (scoreLaw base)
                    (fun cutoff : ℝ =>
                      (M base).posteriorMean
                        (Function.update (theta base) k
                          (standardGaussianLowerTailMean (scoreLaw base) cutoff)))
                    (reportCutoff base) ≤
                  (M base).posteriorMean
                    (Function.update (theta base) k score)) ∧
              (∀ base skill, W.takes base skill) ∧
                (∀ base, ∃ cutoff : ℝ,
                  ∀ score : ℝ, W.reports base score ↔ cutoff ≤ score) := by
  let high : Base → ℝ := fun base =>
    Classical.choose
      (paper_theorem3_1_optional_no_report_mixture_high_endpoint_exists_after
        (hC_nonneg base) (hC_lt_one base) (baseOnlyEstimate base)
        (M base) (theta base) k (scoreLaw base) (low base))
  have hhigh_spec :
      ∀ base,
        low base < high base ∧
          lg21OptionalNoReportMixtureEstimate
              (accessFraction base) (baseOnlyEstimate base) (scoreLaw base)
              (fun cutoff : ℝ =>
                (M base).posteriorMean
                  (Function.update (theta base) k
                    (standardGaussianLowerTailMean (scoreLaw base) cutoff)))
              (high base) <
            (M base).posteriorMean
              (Function.update (theta base) k (high base)) := by
    intro base
    exact Classical.choose_spec
      (paper_theorem3_1_optional_no_report_mixture_high_endpoint_exists_after
        (hC_nonneg base) (hC_lt_one base) (baseOnlyEstimate base)
        (M base) (theta base) k (scoreLaw base) (low base))
  rcases
      paper_theorem3_1_optional_reporting_gaussian_source_witness_of_no_report_mixture_crossings
        M theta k accessFraction baseOnlyEstimate scoreLaw low high
        hC_nonneg hC_lt_one
        (fun base => (hhigh_spec base).1) hleft
        (fun base => (hhigh_spec base).2) with
    ⟨W, reportCutoff, hmem, hindiff, hreports, htakes, hthreshold⟩
  refine ⟨W, reportCutoff, ?_, hindiff, hreports, htakes, hthreshold⟩
  intro base
  exact (hmem base).1

/-
Theorem 3.1 report-required source witness from the source no-take mixture
with the high endpoint chosen automatically.  The only endpoint hypothesis left
is the paper's low-endpoint comparison.
-/
theorem paper_theorem3_1_optional_reporting_gaussian_source_witness_of_no_report_mixture
    {Feature Base : Type*} [Fintype Feature] [DecidableEq Feature]
    [Nonempty Base]
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (accessFraction baseOnlyEstimate : Base → ℝ)
    (scoreLaw : Base → GaussianScaleLaw)
    (hC_nonneg : ∀ base, 0 ≤ accessFraction base)
    (hC_lt_one : ∀ base, accessFraction base < 1) :
    ∃ W : LG21OptionalReportingStrategicWithholdingSourceWitness Base,
      ∃ reportCutoff : Base → ℝ,
        (∀ base,
          lg21OptionalNoReportMixtureEstimate
              (accessFraction base) (baseOnlyEstimate base) (scoreLaw base)
              (fun cutoff : ℝ =>
                (M base).posteriorMean
                  (Function.update (theta base) k
                    (standardGaussianLowerTailMean (scoreLaw base) cutoff)))
              (reportCutoff base) =
            (M base).posteriorMean
              (Function.update (theta base) k (reportCutoff base))) ∧
          (∀ base score,
            W.reports base score ↔
              lg21OptionalNoReportMixtureEstimate
                  (accessFraction base) (baseOnlyEstimate base) (scoreLaw base)
                  (fun cutoff : ℝ =>
                    (M base).posteriorMean
                      (Function.update (theta base) k
                        (standardGaussianLowerTailMean (scoreLaw base) cutoff)))
                  (reportCutoff base) ≤
                (M base).posteriorMean
                  (Function.update (theta base) k score)) ∧
            (∀ base skill, W.takes base skill) ∧
              (∀ base, ∃ cutoff : ℝ,
                ∀ score : ℝ, W.reports base score ↔ cutoff ≤ score) := by
  let low : Base → ℝ := fun base =>
    Classical.choose
      (paper_theorem3_1_optional_no_report_mixture_low_endpoint_exists
        (hC_nonneg base) (hC_lt_one base) (baseOnlyEstimate base)
        (M base) (theta base) k (scoreLaw base))
  have hlow :
      ∀ base,
        (M base).posteriorMean (Function.update (theta base) k (low base)) <
          lg21OptionalNoReportMixtureEstimate
            (accessFraction base) (baseOnlyEstimate base) (scoreLaw base)
            (fun cutoff : ℝ =>
              (M base).posteriorMean
                (Function.update (theta base) k
                  (standardGaussianLowerTailMean (scoreLaw base) cutoff)))
            (low base) := by
    intro base
    exact Classical.choose_spec
      (paper_theorem3_1_optional_no_report_mixture_low_endpoint_exists
        (hC_nonneg base) (hC_lt_one base) (baseOnlyEstimate base)
        (M base) (theta base) k (scoreLaw base))
  rcases
      paper_theorem3_1_optional_reporting_gaussian_source_witness_of_no_report_mixture_low_endpoint
        M theta k accessFraction baseOnlyEstimate scoreLaw low
        hC_nonneg hC_lt_one hlow with
    ⟨W, reportCutoff, _hlow_cutoff, hindiff, hreports, htakes, hthreshold⟩
  exact ⟨W, reportCutoff, hindiff, hreports, htakes, hthreshold⟩

/-
Theorem 3.1 report-required source witness from the source no-take mixture.
The low and high endpoints are both chosen automatically from the Gaussian
lower-tail/Mills asymptotics and positive-slope affine payoff algebra.
-/
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

/-
Singleton-PMF representation of the base- and skill-mixture source surface.
The PMF atoms are the same symbolic law objects used by
`lg21BaseMixedOneTestPosteriorLawSurface`; this gives a finite PMF-facing
surface for theorem routes that are phrased over distributional estimate laws.
-/
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

/-
Concrete Theorem 3.1 optional-reporting PMF surface whose atoms are the
source-shaped skill/base-mixture Gaussian posterior-law objects.
-/
theorem paper_theorem3_1_base_mixed_one_test_posterior_source_law_not_latent_skill_fair
    {Base : Type*} [Nonempty Base]
    (skillGivenBase : Base → PMF ℝ) (baseProfile : PMF Base)
    (intercept slope testScale noAccessEstimate : Base → ℝ)
    (hslope : ∀ base : Base, 0 < slope base)
    (htestScale : ∀ base : Base, 0 < testScale base) :
    ¬ lg21SourceLawLatentSkillFair
      (lg21BaseMixedOneTestPosteriorLawSurface
        skillGivenBase baseProfile intercept slope testScale
        noAccessEstimate hslope htestScale) := by
  let base : Base := Classical.choice inferInstance
  apply lg21_not_lawLatentSkillFair_of_witness PUnit.unit (0 : ℝ) base
  dsimp [lg21BaseMixedOneTestPosteriorLawSurface]
  exact LG21SkillBaseMixtureEstimateLaw.gaussian_ne_point _ _

/-
Theorem 3.1 base/skill-mixture law surface: observable fairness fails because
the access-side observable law is a latent-skill mixture of Gaussians while the
no-access law is a point estimate.
-/
theorem paper_theorem3_1_base_mixed_one_test_posterior_source_law_not_observably_fair
    {Base : Type*} [Nonempty Base]
    (skillGivenBase : Base → PMF ℝ) (baseProfile : PMF Base)
    (intercept slope testScale noAccessEstimate : Base → ℝ)
    (hslope : ∀ base : Base, 0 < slope base)
    (htestScale : ∀ base : Base, 0 < testScale base) :
    ¬ lg21SourceLawObservablyFair
      (lg21BaseMixedOneTestPosteriorLawSurface
        skillGivenBase baseProfile intercept slope testScale
        noAccessEstimate hslope htestScale) := by
  let base : Base := Classical.choice inferInstance
  apply lg21_not_lawObservablyFair_of_witness PUnit.unit base
  dsimp [lg21BaseMixedOneTestPosteriorLawSurface]
  exact LG21SkillBaseMixtureEstimateLaw.skillGaussianMixture_ne_point _ _ _

/-
Theorem 3.1 base/skill-mixture law surface: demographic fairness fails because
the access-side law is a base mixture of skill-conditioned Gaussian mixtures,
while the no-access law is a base mixture of deterministic point estimates.
-/
theorem paper_theorem3_1_base_mixed_one_test_posterior_source_law_not_demographically_fair
    {Base : Type*} [Nonempty Base]
    (skillGivenBase : Base → PMF ℝ) (baseProfile : PMF Base)
    (intercept slope testScale noAccessEstimate : Base → ℝ)
    (hslope : ∀ base : Base, 0 < slope base)
    (htestScale : ∀ base : Base, 0 < testScale base) :
    ¬ lg21SourceLawDemographicallyFair
      (lg21BaseMixedOneTestPosteriorLawSurface
        skillGivenBase baseProfile intercept slope testScale
        noAccessEstimate hslope htestScale) := by
  apply lg21_not_lawDemographicallyFair_of_witness PUnit.unit
  dsimp [lg21BaseMixedOneTestPosteriorLawSurface]
  exact
    LG21SkillBaseMixtureEstimateLaw.baseSkillGaussianMixture_ne_basePointMixture
      baseProfile skillGivenBase
      (fun base skill =>
        lg21OneTestPosteriorScoreLaw
          (intercept base) (slope base) (hslope base)
          skill (testScale base) (htestScale base))
      noAccessEstimate

/-
Theorem 3.1 base/skill-mixture law surface: all three fairness criteria fail.
-/
theorem paper_theorem3_1_base_mixed_one_test_posterior_source_law_not_fair
    {Base : Type*} [Nonempty Base]
    (skillGivenBase : Base → PMF ℝ) (baseProfile : PMF Base)
    (intercept slope testScale noAccessEstimate : Base → ℝ)
    (hslope : ∀ base : Base, 0 < slope base)
    (htestScale : ∀ base : Base, 0 < testScale base) :
    ¬ lg21SourceLawLatentSkillFair
        (lg21BaseMixedOneTestPosteriorLawSurface
          skillGivenBase baseProfile intercept slope testScale
          noAccessEstimate hslope htestScale) ∧
      ¬ lg21SourceLawObservablyFair
        (lg21BaseMixedOneTestPosteriorLawSurface
          skillGivenBase baseProfile intercept slope testScale
          noAccessEstimate hslope htestScale) ∧
        ¬ lg21SourceLawDemographicallyFair
          (lg21BaseMixedOneTestPosteriorLawSurface
            skillGivenBase baseProfile intercept slope testScale
            noAccessEstimate hslope htestScale) :=
  ⟨paper_theorem3_1_base_mixed_one_test_posterior_source_law_not_latent_skill_fair
      skillGivenBase baseProfile intercept slope testScale noAccessEstimate
      hslope htestScale,
    paper_theorem3_1_base_mixed_one_test_posterior_source_law_not_observably_fair
      skillGivenBase baseProfile intercept slope testScale noAccessEstimate
      hslope htestScale,
    paper_theorem3_1_base_mixed_one_test_posterior_source_law_not_demographically_fair
      skillGivenBase baseProfile intercept slope testScale noAccessEstimate
      hslope htestScale⟩

/-
Theorem 3.1 base/skill-mixture singleton-PMF surface: latent-skill fairness
fails because the access-side atom is Gaussian while the no-access atom is a
point estimate.
-/
theorem paper_theorem3_1_optional_reporting_law_strategic_withholding_of_no_report_mixture_and_base_mixed_gaussian_posterior_surface
    {Feature Base : Type*} [Fintype Feature] [DecidableEq Feature] [Nonempty Base]
    (skillGivenBase : Base → PMF ℝ) (baseProfile : PMF Base)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (accessFraction baseOnlyEstimate : Base → ℝ)
    (scoreLaw : Base → GaussianScaleLaw)
    (hC_nonneg : ∀ base, 0 ≤ accessFraction base)
    (hC_lt_one : ∀ base, accessFraction base < 1) :
    ∃ W : LG21OptionalReportingStrategicWithholdingSourceWitness Base,
      (∀ base skill, W.takes base skill) ∧
        (∃ base score, ¬ W.reports base score) ∧
          (∀ base, ∃ cutoff : ℝ,
            ∀ score : ℝ, W.reports base score ↔ cutoff ≤ score) ∧
            ¬ lg21SourceLawLatentSkillFair
              (lg21BaseMixedGaussianPosteriorLawSurface
                skillGivenBase baseProfile M theta k scoreLaw baseOnlyEstimate) ∧
              ¬ lg21SourceLawObservablyFair
                (lg21BaseMixedGaussianPosteriorLawSurface
                  skillGivenBase baseProfile M theta k scoreLaw baseOnlyEstimate) ∧
                ¬ lg21SourceLawDemographicallyFair
                  (lg21BaseMixedGaussianPosteriorLawSurface
                    skillGivenBase baseProfile M theta k scoreLaw baseOnlyEstimate) := by
  rcases
      paper_theorem3_1_optional_reporting_gaussian_source_witness_of_no_report_mixture
        M theta k accessFraction baseOnlyEstimate scoreLaw
        hC_nonneg hC_lt_one with
    ⟨W, _reportCutoff, _hindiff, _hreports, htakes, hthreshold⟩
  have hfair :=
    paper_theorem3_1_base_mixed_one_test_posterior_source_law_not_fair
      skillGivenBase baseProfile
      (fun base => (M base).posteriorMean (Function.update (theta base) k 0))
      (fun base => (M base).centeredFamily.signalWeight k)
      (fun base => (scoreLaw base).scale)
      baseOnlyEstimate
      (fun base => (M base).centeredFamily.signalWeight_pos k)
      (fun base => (scoreLaw base).scale_pos)
  refine ⟨W, htakes, W.some_access_students_do_not_report, hthreshold,
    ?_, ?_, ?_⟩
  · exact hfair.1
  · exact hfair.2.1
  · exact hfair.2.2

/-
Theorem 3.1 report-required law endpoint with a source-shaped skill/base-mixture
posterior surface.  The source no-take mixture supplies the taking cutoff, and
the law surface records observable and demographic mixture structure directly.
-/
theorem paper_theorem3_1_section3_optional_reporting_law_strategic_withholding_for_every_equilibrium_of_no_report_mixture_and_base_mixed_gaussian_posterior_surface
    {Feature Base Equilibrium : Type*}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Base]
    (skillGivenBase : Equilibrium → Base → PMF ℝ)
    (baseProfile : Equilibrium → PMF Base)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (accessFraction baseOnlyEstimate : Equilibrium → Base → ℝ)
    (scoreLaw : Equilibrium → Base → GaussianScaleLaw)
    (hC_nonneg : ∀ e base, 0 ≤ accessFraction e base)
    (hC_lt_one : ∀ e base, accessFraction e base < 1) :
    (∀ (base : Base) (test : ℝ) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      ∀ e : Equilibrium,
        ∃ W : LG21OptionalReportingStrategicWithholdingSourceWitness Base,
          (∀ base skill, W.takes base skill) ∧
            (∃ base score, ¬ W.reports base score) ∧
              (∀ base, ∃ cutoff : ℝ,
                ∀ score : ℝ, W.reports base score ↔ cutoff ≤ score) ∧
              ¬ lg21SourceLawLatentSkillFair
                (lg21BaseMixedGaussianPosteriorLawSurface
                  (skillGivenBase e) (baseProfile e) M theta k
                  (scoreLaw e) (baseOnlyEstimate e)) ∧
                ¬ lg21SourceLawObservablyFair
                  (lg21BaseMixedGaussianPosteriorLawSurface
                    (skillGivenBase e) (baseProfile e) M theta k
                    (scoreLaw e) (baseOnlyEstimate e)) ∧
                  ¬ lg21SourceLawDemographicallyFair
                    (lg21BaseMixedGaussianPosteriorLawSurface
                      (skillGivenBase e) (baseProfile e) M theta k
                      (scoreLaw e) (baseOnlyEstimate e)) := by
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro e
    exact
      paper_theorem3_1_optional_reporting_law_strategic_withholding_of_no_report_mixture_and_base_mixed_gaussian_posterior_surface
        (skillGivenBase e) (baseProfile e) M theta k
        (accessFraction e) (baseOnlyEstimate e) (scoreLaw e)
        (hC_nonneg e) (hC_lt_one e)

/-
Theorem 3.1 report-required Section 3 endpoint over the concrete source-shaped
skill/base-mixture affine-skill posterior-law surface.
-/
end

end LG21TestOptionalPolicies
