import Mathlib

import dep.EconCSLib.Foundations.Probability.Gaussian
import dep.EconCSLib.Foundations.Probability.GaussianMills
open Filter MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal NNReal Real Topology

namespace EconCSLib
namespace Probability

noncomputable section

/- The standard real Gaussian measure, as supplied by mathlib. -/
def standardGaussianMeasure : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)

/- The standard Gaussian CDF, using mathlib's CDF construction. -/
def standardGaussianCDF (x : ℝ) : ℝ :=
  ProbabilityTheory.cdf standardGaussianMeasure x

/- The standard Gaussian density, using mathlib's PDF construction. -/
def standardGaussianDensity (x : ℝ) : ℝ :=
  ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) x

private instance : IsProbabilityMeasure standardGaussianMeasure := by
  unfold standardGaussianMeasure
  infer_instance

private instance : NullSingletonClass standardGaussianMeasure := by
  unfold standardGaussianMeasure
  exact ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num)

private theorem standardGaussianVariance_ne_zero : (1 : ℝ≥0) ≠ 0 := by
  norm_num

theorem continuous_cdf_of_noAtoms
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    Continuous (ProbabilityTheory.cdf μ) := by
  refine continuous_iff_continuousAt.2 ?_
  intro x
  rw [(ProbabilityTheory.monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim]
  rw [StieltjesFunction.rightLim_eq (ProbabilityTheory.cdf μ) x]
  have hsingle_cdf : (ProbabilityTheory.cdf μ).measure ({x} : Set ℝ) = 0 := by
    rw [ProbabilityTheory.measure_cdf μ]
    exact measure_singleton x
  rw [(ProbabilityTheory.cdf μ).measure_singleton x] at hsingle_cdf
  have hleft_le :
      Function.leftLim (ProbabilityTheory.cdf μ) x ≤ ProbabilityTheory.cdf μ x :=
    (ProbabilityTheory.cdf μ).mono.leftLim_le le_rfl
  have hsub_nonneg :
      0 ≤ ProbabilityTheory.cdf μ x - Function.leftLim (ProbabilityTheory.cdf μ) x :=
    sub_nonneg.mpr hleft_le
  have hsub_nonpos :
      ProbabilityTheory.cdf μ x - Function.leftLim (ProbabilityTheory.cdf μ) x ≤ 0 :=
    ENNReal.ofReal_eq_zero.mp hsingle_cdf
  linarith

/- The mathlib-backed standard Gaussian CDF is continuous. -/
theorem standardGaussianCDF_continuous : Continuous standardGaussianCDF := by
  unfold standardGaussianCDF
  exact continuous_cdf_of_noAtoms standardGaussianMeasure

/- The mathlib-backed standard Gaussian CDF is monotone. -/
theorem standardGaussianCDF_mono : Monotone standardGaussianCDF := by
  unfold standardGaussianCDF
  exact ProbabilityTheory.monotone_cdf standardGaussianMeasure

/- Every nonempty half-open interval has positive standard Gaussian mass. -/
theorem standardGaussianMeasure_Ioc_pos {x y : ℝ} (hxy : x < y) :
    0 < standardGaussianMeasure (Ioc x y) := by
  unfold standardGaussianMeasure
  rw [ProbabilityTheory.gaussianReal_apply 0 standardGaussianVariance_ne_zero (Ioc x y)]
  rw [MeasureTheory.setLIntegral_pos_iff
    (ProbabilityTheory.measurable_gaussianPDF 0 (1 : ℝ≥0))]
  rw [ProbabilityTheory.support_gaussianPDF
    (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) standardGaussianVariance_ne_zero]
  rw [univ_inter, Real.volume_Ioc]
  exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hxy)

/- Every nonempty half-open interval has positive mass under a nondegenerate Gaussian. -/
namespace GaussianScaleLaw

/- The mathlib variance parameter associated with a positive scale law. -/
end GaussianScaleLaw

/- The standard Gaussian measure gives positive mass to every nonempty open set. -/
theorem standardGaussianCDF_strictMono : StrictMono standardGaussianCDF := by
  intro x y hxy
  have hmass : 0 < standardGaussianMeasure (Ioc x y) :=
    standardGaussianMeasure_Ioc_pos hxy
  have hmeasure_cdf :
      (ProbabilityTheory.cdf standardGaussianMeasure).measure (Ioc x y) =
        standardGaussianMeasure (Ioc x y) := by
    rw [ProbabilityTheory.measure_cdf standardGaussianMeasure]
  have hst := (ProbabilityTheory.cdf standardGaussianMeasure).measure_Ioc x y
  have hofReal_pos :
      0 < ENNReal.ofReal (standardGaussianCDF y - standardGaussianCDF x) := by
    change
      0 < ENNReal.ofReal
        (ProbabilityTheory.cdf standardGaussianMeasure y -
          ProbabilityTheory.cdf standardGaussianMeasure x)
    rw [← hst, hmeasure_cdf]
    exact hmass
  have hsub_pos : 0 < standardGaussianCDF y - standardGaussianCDF x :=
    ENNReal.ofReal_pos.mp hofReal_pos
  linarith

/- The standard Gaussian measure is symmetric around zero. -/
theorem standardGaussianMeasure_map_neg :
    standardGaussianMeasure.map (fun x : ℝ => -x) = standardGaussianMeasure := by
  unfold standardGaussianMeasure
  simpa using
    (ProbabilityTheory.gaussianReal_map_neg
      (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))

/- The mathlib-backed standard Gaussian CDF takes value `1 / 2` at zero. -/
theorem standardGaussianCDF_zero_eq_half :
    standardGaussianCDF 0 = (1 / 2 : ℝ) := by
  unfold standardGaussianCDF
  rw [ProbabilityTheory.cdf_eq_real]
  have hIicIci_measure :
      standardGaussianMeasure (Iic (0 : ℝ)) =
        standardGaussianMeasure (Ici (0 : ℝ)) := by
    calc
      standardGaussianMeasure (Iic (0 : ℝ))
          = (standardGaussianMeasure.map (fun x : ℝ => -x)) (Iic (0 : ℝ)) := by
              rw [standardGaussianMeasure_map_neg]
      _ = standardGaussianMeasure
          ((fun x : ℝ => -x) ⁻¹' Iic (0 : ℝ)) := by
              rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
      _ = standardGaussianMeasure (Ici (0 : ℝ)) := by
              congr 1
              ext x
              simp
  have hIicIci_real :
      standardGaussianMeasure.real (Iic (0 : ℝ)) =
        standardGaussianMeasure.real (Ici (0 : ℝ)) := by
    simp [measureReal_def, hIicIci_measure]
  have hIciIoi_real :
      standardGaussianMeasure.real (Ici (0 : ℝ)) =
        standardGaussianMeasure.real (Ioi (0 : ℝ)) := by
    simpa using
      (MeasureTheory.measureReal_congr
        (μ := standardGaussianMeasure)
        ((MeasureTheory.Ioi_ae_eq_Ici
          (μ := standardGaussianMeasure) (a := (0 : ℝ))).symm))
  have hsym :
      standardGaussianMeasure.real (Iic (0 : ℝ)) =
        standardGaussianMeasure.real (Ioi (0 : ℝ)) :=
    hIicIci_real.trans hIciIoi_real
  have hcompl :
      standardGaussianMeasure.real (Ioi (0 : ℝ)) =
        1 - standardGaussianMeasure.real (Iic (0 : ℝ)) := by
    simpa using
      (MeasureTheory.probReal_compl_eq_one_sub
        (μ := standardGaussianMeasure) (s := Iic (0 : ℝ)) measurableSet_Iic)
  linarith

/- Symmetry of the mathlib-backed standard Gaussian CDF. -/
theorem standardGaussianCDF_neg_eq_one_sub (z : ℝ) :
    standardGaussianCDF (-z) = 1 - standardGaussianCDF z := by
  unfold standardGaussianCDF
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real]
  have hIicIci_measure :
      standardGaussianMeasure (Iic (-z)) =
        standardGaussianMeasure (Ici z) := by
    calc
      standardGaussianMeasure (Iic (-z))
          = (standardGaussianMeasure.map (fun x : ℝ => -x)) (Iic (-z)) := by
              rw [standardGaussianMeasure_map_neg]
      _ = standardGaussianMeasure
          ((fun x : ℝ => -x) ⁻¹' Iic (-z)) := by
              rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
      _ = standardGaussianMeasure (Ici z) := by
              congr 1
              ext x
              simp
  have hIicIci_real :
      standardGaussianMeasure.real (Iic (-z)) =
        standardGaussianMeasure.real (Ici z) := by
    simp [measureReal_def, hIicIci_measure]
  have hIciIoi_real :
      standardGaussianMeasure.real (Ici z) =
        standardGaussianMeasure.real (Ioi z) := by
    simpa using
      (MeasureTheory.measureReal_congr
        (μ := standardGaussianMeasure)
        ((MeasureTheory.Ioi_ae_eq_Ici
          (μ := standardGaussianMeasure) (a := z)).symm))
  have hcompl :
      standardGaussianMeasure.real (Ioi z) =
        1 - standardGaussianMeasure.real (Iic z) := by
    simpa using
      (MeasureTheory.probReal_compl_eq_one_sub
        (μ := standardGaussianMeasure) (s := Iic z) measurableSet_Iic)
  linarith

/- The mathlib-backed standard Gaussian density is nonnegative. -/
theorem standardGaussianDensity_nonneg (z : ℝ) :
    0 ≤ standardGaussianDensity z := by
  unfold standardGaussianDensity
  exact ProbabilityTheory.gaussianPDFReal_nonneg 0 (1 : ℝ≥0) z

/- The mathlib-backed standard Gaussian density is strictly positive. -/
theorem standardGaussianDensity_pos (z : ℝ) :
    0 < standardGaussianDensity z := by
  unfold standardGaussianDensity
  exact ProbabilityTheory.gaussianPDFReal_pos
    0 (1 : ℝ≥0) z standardGaussianVariance_ne_zero

/-
The mathlib-backed standard Gaussian density in elementary normalized form.
-/
theorem standardGaussianDensity_eq_mills_integrand (z : ℝ) :
    standardGaussianDensity z =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(z ^ 2) / 2) := by
  unfold standardGaussianDensity
  rw [ProbabilityTheory.gaussianPDFReal_def]
  simp

/- Symmetry of the mathlib-backed standard Gaussian density. -/
theorem standardGaussianCDF_nonneg (z : ℝ) :
    0 ≤ standardGaussianCDF z := by
  unfold standardGaussianCDF
  exact ProbabilityTheory.cdf_nonneg standardGaussianMeasure z

/- The mathlib-backed standard Gaussian CDF is bounded by one. -/
theorem standardGaussianCDF_le_one (z : ℝ) :
    standardGaussianCDF z ≤ 1 := by
  unfold standardGaussianCDF
  exact ProbabilityTheory.cdf_le_one standardGaussianMeasure z

/- The mathlib-backed standard Gaussian CDF is strictly positive. -/
theorem standardGaussianCDF_lt_one (z : ℝ) :
    standardGaussianCDF z < 1 := by
  have hmono := standardGaussianCDF_strictMono
    (show z < z + 1 by linarith)
  have hle := standardGaussianCDF_le_one (z + 1)
  linarith

/- The mathlib-backed standard Gaussian upper tail is strictly positive. -/
theorem standardGaussianTail_pos (z : ℝ) :
    0 < 1 - standardGaussianCDF z := by
  have hlt := standardGaussianCDF_lt_one z
  linarith

/- The mathlib-backed standard Gaussian upper tail as a density integral. -/
theorem standardGaussianTail_eq_const_mul_millsTail (z : ℝ) :
    1 - standardGaussianCDF z =
      (Real.sqrt (2 * Real.pi))⁻¹ * gaussianMillsTail z := by
  have hcompl :
      standardGaussianMeasure.real (Ioi z) = 1 - standardGaussianCDF z := by
    simpa [standardGaussianCDF, ProbabilityTheory.cdf_eq_real, compl_Iic] using
      (MeasureTheory.probReal_compl_eq_one_sub
        (μ := standardGaussianMeasure) (s := Iic z) measurableSet_Iic)
  have hmeasure :
      standardGaussianMeasure (Ioi z) =
        ENNReal.ofReal (∫ x in Ioi z, standardGaussianDensity x) := by
    unfold standardGaussianMeasure standardGaussianDensity
    simpa using
      (ProbabilityTheory.gaussianReal_apply_eq_integral
        0 standardGaussianVariance_ne_zero (Ioi z))
  have htail_integral :
      standardGaussianMeasure.real (Ioi z) =
        ∫ x in Ioi z, standardGaussianDensity x := by
    rw [measureReal_def, hmeasure]
    rw [ENNReal.toReal_ofReal]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioi
      (fun x _hx => standardGaussianDensity_nonneg x)
  have hintegral :
      (∫ x in Ioi z, standardGaussianDensity x) =
        (Real.sqrt (2 * Real.pi))⁻¹ * gaussianMillsTail z := by
    calc
      (∫ x in Ioi z, standardGaussianDensity x)
          = ∫ x in Ioi z,
              (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
              exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
                (fun x _hx => standardGaussianDensity_eq_mills_integrand x)
      _ = (Real.sqrt (2 * Real.pi))⁻¹ *
            ∫ x in Ioi z, Real.exp (-(x ^ 2) / 2) := by
              rw [integral_const_mul]
      _ = (Real.sqrt (2 * Real.pi))⁻¹ * gaussianMillsTail z := by
              rfl
  rw [← hcompl, htail_integral, hintegral]

/- The mathlib-backed standard Gaussian CDF tends to zero at `-∞`. -/
def standardGaussianHazard (z : ℝ) : ℝ :=
  standardGaussianDensity z / (1 - standardGaussianCDF z)

@[simp] theorem standardGaussianHazard_eq (z : ℝ) :
    standardGaussianHazard z =
      standardGaussianDensity z / (1 - standardGaussianCDF z) := rfl

/-
Left-tail CDF times right-tail hazard equals the density.  This is the
Gaussian symmetry identity used to control lower-tail conditional means.
-/
theorem standardGaussianCDF_neg_mul_hazard (t : ℝ) :
    standardGaussianCDF (-t) * standardGaussianHazard t =
      standardGaussianDensity t := by
  rw [standardGaussianCDF_neg_eq_one_sub, standardGaussianHazard_eq]
  field_simp [(standardGaussianTail_pos t).ne']

/- The mathlib-backed standard normal hazard rate is strictly positive. -/
theorem standardGaussianHazard_pos (z : ℝ) :
    0 < standardGaussianHazard z := by
  rw [standardGaussianHazard_eq]
  exact div_pos (standardGaussianDensity_pos z) (standardGaussianTail_pos z)

/-
The mathlib-backed standard-normal hazard is the reciprocal of the unnormalized
Gaussian Mills ratio.
-/
theorem standardGaussianHazard_eq_millsHazard (z : ℝ) :
    standardGaussianHazard z = gaussianMillsHazard z := by
  rw [standardGaussianHazard_eq, standardGaussianDensity_eq_mills_integrand,
    standardGaussianTail_eq_const_mul_millsTail]
  unfold gaussianMillsHazard gaussianMillsRatio
  field_simp [Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * Real.pi),
    gaussianMillsTail_pos z, Real.exp_pos (z ^ 2 / 2)]
  rw [← Real.exp_add]
  have hsum : -(z ^ 2 / 2) + z ^ 2 / 2 = 0 := by ring
  rw [hsum, Real.exp_zero]

/-
Concrete lower-tail conditional mean for a location-scale standard-normal law,
expressed by symmetry through the upper-tail hazard.
-/
def standardGaussianLowerTailMean
    (L : GaussianScaleLaw) (threshold : ℝ) : ℝ :=
  L.mean - L.scale * standardGaussianHazard (-(L.standardize threshold))

/-
The concrete Gaussian lower-tail mean is strictly below the threshold.
-/
theorem standardGaussianLowerTailMean_lt_threshold
    (L : GaussianScaleLaw) (threshold : ℝ) :
    standardGaussianLowerTailMean L threshold < threshold := by
  let z : ℝ := L.standardize threshold
  have hthreshold_std :
      L.mean + L.scale * L.standardize threshold = threshold := by
    simpa [GaussianScaleLaw.unstandardize] using
      L.unstandardize_standardize threshold
  have hcore : -standardGaussianHazard (-z) < z := by
    by_cases hz_nonneg : 0 ≤ z
    · have hhaz_pos : 0 < standardGaussianHazard (-z) :=
        standardGaussianHazard_pos (-z)
      linarith
    · have hz_neg : z < 0 := lt_of_not_ge hz_nonneg
      have hneg_pos : 0 < -z := by linarith
      have hhaz_gt : -z < standardGaussianHazard (-z) := by
        rw [standardGaussianHazard_eq_millsHazard]
        exact gaussianMillsHazard_gt_arg_of_pos hneg_pos
      linarith
  have hmul :
      L.scale * (-standardGaussianHazard (-z)) < L.scale * z :=
    mul_lt_mul_of_pos_left hcore L.scale_pos
  calc
    standardGaussianLowerTailMean L threshold =
        L.mean + L.scale * (-standardGaussianHazard (-z)) := by
      dsimp [standardGaussianLowerTailMean, z]
      ring
    _ < L.mean + L.scale * z := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_lt_add_left hmul L.mean
    _ = threshold := by
      dsimp [z]
      exact hthreshold_std

/-
Concrete Gaussian lower-tail mean certificate backed by mathlib's Gaussian CDF
and the Mills-ratio hazard facts.
-/
theorem standardGaussianDensity_continuous :
    Continuous standardGaussianDensity := by
  unfold standardGaussianDensity ProbabilityTheory.gaussianPDFReal
  fun_prop

/- Product of the standard Gaussian density with an affine-shifted density is integrable on
every upper tail. -/
theorem standardGaussianHazard_continuous :
    Continuous standardGaussianHazard := by
  unfold standardGaussianHazard
  exact standardGaussianDensity_continuous.div
    (continuous_const.sub standardGaussianCDF_continuous)
    (fun z => (standardGaussianTail_pos z).ne')

/-
For a fixed Gaussian location-scale law, the concrete lower-tail conditional
mean is continuous in the finite threshold.
-/
theorem standardGaussianLowerTailMean_continuous (L : GaussianScaleLaw) :
    Continuous (fun threshold : ℝ =>
      standardGaussianLowerTailMean L threshold) := by
  dsimp [standardGaussianLowerTailMean]
  have hstd : Continuous (fun threshold : ℝ => L.standardize threshold) := by
    unfold GaussianScaleLaw.standardize
    fun_prop
  exact continuous_const.sub
    (continuous_const.mul (standardGaussianHazard_continuous.comp hstd.neg))

/- The standard Gaussian density tends to zero at `-∞`. -/
theorem standardGaussianDensity_tendsto_atTop_zero :
    Tendsto standardGaussianDensity atTop (𝓝 0) := by
  have hconst :=
    (tendsto_const_nhds
      (x := (Real.sqrt (2 * Real.pi))⁻¹)).mul
        gaussianExpFactor_tendsto_atTop_zero
  have hdensity :
      Tendsto standardGaussianDensity atTop
        (𝓝 ((Real.sqrt (2 * Real.pi))⁻¹ * 0)) := by
    refine hconst.congr' ?_
    filter_upwards with t
    rw [standardGaussianDensity_eq_mills_integrand]
  simpa using hdensity

/-
Integration-by-parts identity for the affine-CDF first moment on an upper
tail, assuming the two integration-by-parts terms are integrable.

`offset = A * sqrt(1+c^2)`.
-/
theorem standardGaussianCDF_neg_mul_id_tendsto_atTop_zero :
    Tendsto (fun t : ℝ => standardGaussianCDF (-t) * t) atTop (𝓝 0) := by
  let normalizingConst : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  have hconst_nonneg : 0 ≤ normalizingConst := by
    dsimp [normalizingConst]
    exact inv_nonneg.mpr
      (Real.sqrt_nonneg (2 * Real.pi))
  have hconst_exp :
      Tendsto (fun t : ℝ =>
          normalizingConst * Real.exp (-(t ^ 2) / 2))
        atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds (x := normalizingConst)).mul
        gaussianExpFactor_tendsto_atTop_zero
  refine squeeze_zero' ?_ ?_ hconst_exp
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact mul_nonneg (standardGaussianCDF_nonneg (-t)) ht
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have htail_lt :
        gaussianMillsTail t < Real.exp (-(t ^ 2) / 2) / t := by
      simpa [gaussianMillsUpperGap, sub_pos] using
        gaussianMillsUpperGap_pos_of_pos ht
    have htail_mul_le :
        gaussianMillsTail t * t ≤ Real.exp (-(t ^ 2) / 2) := by
      have hmul := mul_lt_mul_of_pos_right htail_lt ht
      have hright :
          (Real.exp (-(t ^ 2) / 2) / t) * t =
            Real.exp (-(t ^ 2) / 2) := by
        field_simp [ht.ne']
      exact le_of_lt (by simpa [hright] using hmul)
    calc
      standardGaussianCDF (-t) * t =
          (1 - standardGaussianCDF t) * t := by
            rw [standardGaussianCDF_neg_eq_one_sub]
      _ = (normalizingConst * gaussianMillsTail t) * t := by
            rw [standardGaussianTail_eq_const_mul_millsTail]
      _ = normalizingConst * (gaussianMillsTail t * t) := by ring
      _ ≤ normalizingConst * Real.exp (-(t ^ 2) / 2) :=
            mul_le_mul_of_nonneg_left htail_mul_le hconst_nonneg

/-
The product of a left-tail probability with the lower-tail hazard gap tends to
zero.  Equivalently, `Φ(-t) * (t - h(t)) -> 0` for the standard normal hazard
`h`.
-/
theorem standardGaussianCDF_neg_mul_hazard_gap_tendsto_atTop_zero :
    Tendsto
      (fun t : ℝ =>
        standardGaussianCDF (-t) * (t - standardGaussianHazard t))
      atTop (𝓝 0) := by
  have hdiff :=
    standardGaussianCDF_neg_mul_id_tendsto_atTop_zero.sub
      standardGaussianDensity_tendsto_atTop_zero
  have hdiff_zero :
      Tendsto
        (fun t : ℝ => standardGaussianCDF (-t) * t - standardGaussianDensity t)
        atTop (𝓝 0) := by
    simpa using hdiff
  refine hdiff_zero.congr' ?_
  filter_upwards with t
  rw [mul_sub, standardGaussianCDF_neg_mul_hazard]

/-
For any Gaussian location-scale law, the lower-tail conditional-mean gap is
small after multiplying by the left-tail mass.
-/
theorem standardGaussian_normalCDF_mul_lowerTailMean_sub_tendsto_atBot
    (L : GaussianScaleLaw) :
    Tendsto
      (fun cutoff : ℝ =>
        standardGaussianCDF (L.standardize cutoff) *
          (standardGaussianLowerTailMean L cutoff - cutoff))
      atBot (𝓝 0) := by
  have hstd :
      Tendsto (fun cutoff : ℝ => L.standardize cutoff) atBot atBot := by
    have hscale_inv_pos : 0 < L.scale⁻¹ := inv_pos.mpr L.scale_pos
    have hmul :
        Tendsto
          (fun cutoff : ℝ =>
            L.scale⁻¹ * cutoff + (-L.mean / L.scale))
          atBot atBot :=
      ((Filter.tendsto_const_mul_atBot_of_pos hscale_inv_pos).2
        Filter.tendsto_id).atBot_add tendsto_const_nhds
    convert hmul using 1
    ext cutoff
    rw [GaussianScaleLaw.standardize]
    field_simp [ne_of_gt L.scale_pos]
    ring
  have hneg :
      Tendsto (fun cutoff : ℝ => -L.standardize cutoff) atBot atTop :=
    tendsto_neg_atBot_atTop.comp hstd
  have htail :=
    standardGaussianCDF_neg_mul_hazard_gap_tendsto_atTop_zero.comp hneg
  have hscaled :=
    (tendsto_const_nhds (x := L.scale)).mul htail
  have hscaled_zero :
      Tendsto
        (fun cutoff : ℝ =>
          L.scale *
            (standardGaussianCDF (-(-L.standardize cutoff)) *
              ((-L.standardize cutoff) -
                standardGaussianHazard (-L.standardize cutoff))))
        atBot (𝓝 (L.scale * 0)) := by
    simpa using hscaled
  have hscaled_zero' :
      Tendsto
        (fun cutoff : ℝ =>
          L.scale *
            (standardGaussianCDF (-(-L.standardize cutoff)) *
              ((-L.standardize cutoff) -
                standardGaussianHazard (-L.standardize cutoff))))
        atBot (𝓝 0) := by
    simpa only [mul_zero] using hscaled_zero
  refine hscaled_zero'.congr' ?_
  filter_upwards with cutoff
  have hcutoff :
      L.mean + L.scale * L.standardize cutoff = cutoff := by
    simpa [GaussianScaleLaw.unstandardize] using
      L.unstandardize_standardize cutoff
  have hsub :
      standardGaussianLowerTailMean L cutoff - cutoff =
        L.scale *
          ((-L.standardize cutoff) -
            standardGaussianHazard (-L.standardize cutoff)) := by
    have hscale_std : L.scale * L.standardize cutoff = cutoff - L.mean := by
      linarith
    dsimp [standardGaussianLowerTailMean]
    nlinarith
  calc
    L.scale *
        (standardGaussianCDF (-(-L.standardize cutoff)) *
          ((-L.standardize cutoff) -
            standardGaussianHazard (-L.standardize cutoff)))
        =
      L.scale *
        (standardGaussianCDF (L.standardize cutoff) *
          ((-L.standardize cutoff) -
            standardGaussianHazard (-L.standardize cutoff))) := by
          ring_nf
    _ =
      standardGaussianCDF (L.standardize cutoff) *
        (standardGaussianLowerTailMean L cutoff - cutoff) := by
          rw [hsub]
          ring

/- The standard normal hazard tends to zero at `-∞`. -/
def standardGaussianCDFAPI : StandardGaussianCDFAPI where
  cdf := standardGaussianCDF
  density := standardGaussianDensity
  cdf_continuous := standardGaussianCDF_continuous
  cdf_mono := standardGaussianCDF_mono
  cdf_strictMono := standardGaussianCDF_strictMono
  cdf_zero_eq_half := standardGaussianCDF_zero_eq_half
  density_nonneg := standardGaussianDensity_nonneg
  cdf_nonneg := standardGaussianCDF_nonneg
  cdf_le_one := standardGaussianCDF_le_one

/- Concrete standard-normal derivative API backed by mathlib's Gaussian CDF/PDF. -/
end

end Probability
end EconCSLib
