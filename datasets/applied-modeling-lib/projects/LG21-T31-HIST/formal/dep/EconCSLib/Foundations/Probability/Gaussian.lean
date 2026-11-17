import Mathlib

import dep.EconCSLib.Foundations.Math.AffineThreshold

open scoped BigOperators

namespace EconCSLib
namespace Probability

noncomputable section

/-!
# Gaussian Algebra and Testing-Paper Interfaces

Reusable Gaussian-facing algebra for admissions/testing papers.

This file deliberately separates two layers:

1. exact conjugate-normal precision algebra, which is formalized here; and
2. analytic normal CDF/density/hazard facts, which are exposed through API
   records. `GaussianMathlib` instantiates the basic CDF/density API from
   mathlib's `ProbabilityTheory.gaussianReal` and Gaussian PDF facts; quantile
   and inverse-Mills/hazard facts remain separate analytic interfaces.

## Main declarations

- `GaussianVarianceLaw`, `GaussianScaleLaw`
- `StandardGaussianCDFAPI`
- `GaussianLowerTailMeanCertificate`
- `GaussianPriorSignal`
- `GaussianSignalFamily`
- `GaussianOffsetSignalFamily`
- `GaussianOffsetSignalFamily.conditionalPosteriorMeanScaleLaw`
- `GaussianHazardCertificate`
-/

/- A Gaussian law represented by mean and variance. -/
structure GaussianVarianceLaw where
  mean : ℝ
  variance : ℝ
  variance_pos : 0 < variance

/- A Gaussian location-scale law represented by mean and positive scale. -/
structure GaussianScaleLaw where
  mean : ℝ
  scale : ℝ
  scale_pos : 0 < scale

namespace GaussianScaleLaw

/- Standardize a value relative to a Gaussian location-scale law. -/
def standardize (L : GaussianScaleLaw) (x : ℝ) : ℝ :=
  (x - L.mean) / L.scale

/- Undo standardization relative to a Gaussian location-scale law. -/
def unstandardize (L : GaussianScaleLaw) (z : ℝ) : ℝ :=
  L.mean + L.scale * z

theorem unstandardize_standardize (L : GaussianScaleLaw) (x : ℝ) :
    L.unstandardize (L.standardize x) = x := by
  rw [standardize, unstandardize]
  calc
    L.mean + L.scale * ((x - L.mean) / L.scale) =
        L.mean + (x - L.mean) := by
      rw [mul_div_cancel₀ _ (ne_of_gt L.scale_pos)]
    _ = x := by
      ring

def affineImage (L : GaussianScaleLaw) (a b : ℝ) (hb : 0 < b) :
    GaussianScaleLaw where
  mean := a + b * L.mean
  scale := b * L.scale
  scale_pos := mul_pos hb L.scale_pos

end GaussianScaleLaw

/-
Abstract standard-normal CDF/density API.

Analytic papers can instantiate this once a concrete normal CDF/density library
is available. Until then, paper-specific Gaussian proofs can state exactly
which normal facts they require without hiding them in theorem conclusions.
-/
structure StandardGaussianCDFAPI where
  cdf : ℝ → ℝ
  density : ℝ → ℝ
  cdf_continuous : Continuous cdf
  cdf_mono : Monotone cdf
  cdf_strictMono : StrictMono cdf
  cdf_zero_eq_half : cdf 0 = (1 / 2 : ℝ)
  density_nonneg : ∀ z, 0 ≤ density z
  cdf_nonneg : ∀ z, 0 ≤ cdf z
  cdf_le_one : ∀ z, cdf z ≤ 1

namespace StandardGaussianCDFAPI

/- Normal CDF for an arbitrary location-scale law by standardization. -/
def normalCDF (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (x : ℝ) : ℝ :=
  api.cdf (L.standardize x)

/- Normal upper tail for an arbitrary location-scale law. -/
theorem normalCDF_continuous (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) :
    Continuous (api.normalCDF L) := by
  have hstd : Continuous L.standardize := by
    unfold GaussianScaleLaw.standardize
    fun_prop
  exact api.cdf_continuous.comp hstd

theorem normalCDF_nonneg (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (x : ℝ) :
    0 ≤ api.normalCDF L x :=
  api.cdf_nonneg (L.standardize x)

section Mixture

variable {γ : Type*} [Fintype γ]

/- Weighted admission mass above a common threshold for finitely many Gaussian groups. -/
namespace MixtureThresholdCertificate

end MixtureThresholdCertificate

end Mixture

end StandardGaussianCDFAPI

/-
Certificate-level interface for the conditional mean below a threshold for a
location-scale Gaussian.

The concrete formula can be instantiated from a normal CDF/density library.
Many admissions/testing proofs only need the order fact that a nondegenerate
Gaussian conditional mean below a finite threshold lies strictly below that
threshold, so this lightweight certificate keeps those paper proofs independent
of the analytic lower-tail formula.
-/
namespace GaussianLowerTailMeanCertificate

end GaussianLowerTailMeanCertificate

namespace GaussianVarianceLaw

/- Nondegenerate affine image of a Gaussian variance law. -/
def affineImage (L : GaussianVarianceLaw) (a b : ℝ) (hb : b ≠ 0) :
    GaussianVarianceLaw where
  mean := a + b * L.mean
  variance := b ^ 2 * L.variance
  variance_pos := by
    exact mul_pos (sq_pos_of_ne_zero hb) L.variance_pos

end GaussianVarianceLaw

/-
Conjugate Gaussian model with one noisy signal:

`θ ~ N(priorMean, priorVar)` and `x = θ + noise`, `noiseVar > 0`.
-/
structure GaussianPriorSignal where
  priorMean : ℝ
  priorVar : ℝ
  noiseVar : ℝ
  priorVar_pos : 0 < priorVar
  noiseVar_pos : 0 < noiseVar

namespace GaussianPriorSignal

def priorPrecision (M : GaussianPriorSignal) : ℝ :=
  M.priorVar⁻¹

def noisePrecision (M : GaussianPriorSignal) : ℝ :=
  M.noiseVar⁻¹

def posteriorPrecision (M : GaussianPriorSignal) : ℝ :=
  M.priorPrecision + M.noisePrecision

def posteriorVariance (M : GaussianPriorSignal) : ℝ :=
  M.posteriorPrecision⁻¹

def priorWeight (M : GaussianPriorSignal) : ℝ :=
  M.noiseVar / (M.priorVar + M.noiseVar)

def signalWeight (M : GaussianPriorSignal) : ℝ :=
  M.priorVar / (M.priorVar + M.noiseVar)

/- Posterior mean after observing signal value `x`. -/
def posteriorMean (M : GaussianPriorSignal) (x : ℝ) : ℝ :=
  M.posteriorVariance *
    (M.priorPrecision * M.priorMean + M.noisePrecision * x)

/- Marginal variance of the posterior mean as a random variable. -/
theorem priorPrecision_pos (M : GaussianPriorSignal) :
    0 < M.priorPrecision := by
  exact inv_pos.mpr M.priorVar_pos

theorem noisePrecision_pos (M : GaussianPriorSignal) :
    0 < M.noisePrecision := by
  exact inv_pos.mpr M.noiseVar_pos

theorem posteriorPrecision_pos (M : GaussianPriorSignal) :
    0 < M.posteriorPrecision := by
  exact add_pos M.priorPrecision_pos M.noisePrecision_pos

theorem posteriorVariance_pos (M : GaussianPriorSignal) :
    0 < M.posteriorVariance := by
  exact inv_pos.mpr M.posteriorPrecision_pos

theorem signalWeight_pos (M : GaussianPriorSignal) :
    0 < M.signalWeight := by
  exact div_pos M.priorVar_pos (add_pos M.priorVar_pos M.noiseVar_pos)

end GaussianPriorSignal

/- Conjugate Gaussian model with a finite family of noisy signals. -/
structure GaussianSignalFamily (ι : Type*) [Fintype ι] where
  priorMean : ℝ
  priorVar : ℝ
  noiseVar : ι → ℝ
  priorVar_pos : 0 < priorVar
  noiseVar_pos : ∀ i, 0 < noiseVar i

namespace GaussianSignalFamily

variable {ι : Type*} [Fintype ι]

def priorPrecision (M : GaussianSignalFamily ι) : ℝ :=
  M.priorVar⁻¹

def signalPrecision (M : GaussianSignalFamily ι) (i : ι) : ℝ :=
  (M.noiseVar i)⁻¹

def signalPrecisionSum (M : GaussianSignalFamily ι) : ℝ :=
  ∑ i : ι, M.signalPrecision i

def posteriorPrecision (M : GaussianSignalFamily ι) : ℝ :=
  M.priorPrecision + ∑ i : ι, M.signalPrecision i

def posteriorVariance (M : GaussianSignalFamily ι) : ℝ :=
  M.posteriorPrecision⁻¹

def priorWeight (M : GaussianSignalFamily ι) : ℝ :=
  M.posteriorVariance * M.priorPrecision

def signalWeight (M : GaussianSignalFamily ι) (i : ι) : ℝ :=
  M.posteriorVariance * M.signalPrecision i

/- Posterior mean from a finite vector of observed signal values. -/
def posteriorMean (M : GaussianSignalFamily ι) (x : ι → ℝ) : ℝ :=
  M.posteriorVariance *
    (M.priorPrecision * M.priorMean +
      ∑ i : ι, M.signalPrecision i * x i)

theorem priorPrecision_pos (M : GaussianSignalFamily ι) :
    0 < M.priorPrecision := by
  exact inv_pos.mpr M.priorVar_pos

theorem signalPrecision_pos (M : GaussianSignalFamily ι) (i : ι) :
    0 < M.signalPrecision i := by
  exact inv_pos.mpr (M.noiseVar_pos i)

theorem signalPrecisionSum_nonneg (M : GaussianSignalFamily ι) :
    0 ≤ M.signalPrecisionSum := by
  exact Finset.sum_nonneg (by
    intro i _
    exact (M.signalPrecision_pos i).le)

theorem posteriorPrecision_pos (M : GaussianSignalFamily ι) :
    0 < M.posteriorPrecision := by
  exact add_pos_of_pos_of_nonneg M.priorPrecision_pos
    (by simpa [signalPrecisionSum] using M.signalPrecisionSum_nonneg)

theorem posteriorVariance_pos (M : GaussianSignalFamily ι) :
    0 < M.posteriorVariance := by
  exact inv_pos.mpr M.posteriorPrecision_pos

theorem signalWeight_pos (M : GaussianSignalFamily ι) (i : ι) :
    0 < M.signalWeight i := by
  exact mul_pos M.posteriorVariance_pos (M.signalPrecision_pos i)

theorem posteriorMean_eq_weighted_sum
    (M : GaussianSignalFamily ι) (x : ι → ℝ) :
    M.posteriorMean x =
      M.priorWeight * M.priorMean +
        ∑ i : ι, M.signalWeight i * x i := by
  change
    M.posteriorVariance *
        (M.priorPrecision * M.priorMean +
          ∑ i : ι, M.signalPrecision i * x i) =
      (M.posteriorVariance * M.priorPrecision) * M.priorMean +
        ∑ i : ι, (M.posteriorVariance * M.signalPrecision i) * x i
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl (by
      intro i _
      ring)

/-
Posterior mean in the source-paper precision-weighted form:
prior precision times prior mean plus signal precisions times observed signals,
divided by total posterior precision.
-/
theorem posteriorMean_lt_of_pointwise_le_exists_lt
    (M : GaussianSignalFamily ι) {x y : ι → ℝ}
    (hxy : ∀ i, x i ≤ y i) (j : ι) (hstrict : x j < y j) :
    M.posteriorMean x < M.posteriorMean y := by
  dsimp [posteriorMean]
  refine mul_lt_mul_of_pos_left ?_ M.posteriorVariance_pos
  have hsum_lt :
      (∑ i : ι, M.signalPrecision i * x i) <
        ∑ i : ι, M.signalPrecision i * y i := by
    exact Finset.sum_lt_sum (by
      intro i _
      exact mul_le_mul_of_nonneg_left (hxy i) (M.signalPrecision_pos i).le)
      ⟨j, ⟨Finset.mem_univ j,
        mul_lt_mul_of_pos_left hstrict (M.signalPrecision_pos j)⟩⟩
  simpa [add_comm, add_left_comm, add_assoc] using
    add_lt_add_left hsum_lt (M.priorPrecision * M.priorMean)

/- Holding all other coordinates fixed, the posterior mean is strictly
increasing in any one observed signal. -/
theorem posteriorMean_update_strictMono [DecidableEq ι]
    (M : GaussianSignalFamily ι) (x : ι → ℝ) (j : ι) :
    StrictMono (fun z : ℝ => M.posteriorMean (Function.update x j z)) := by
  intro a b hab
  refine M.posteriorMean_lt_of_pointwise_le_exists_lt ?_ j ?_
  · intro i
    by_cases h : i = j
    · subst h
      simp [Function.update, hab.le]
    · simp [Function.update, h]
  · simp [Function.update, hab]

/-
Holding all other coordinates fixed, the posterior mean is an affine function
of the selected coordinate, with slope equal to that coordinate's posterior
weight.
-/
theorem posteriorMean_update_eq_base_add_weight_mul_sub [DecidableEq ι]
    (M : GaussianSignalFamily ι) (x : ι → ℝ) (j : ι) (base z : ℝ) :
    M.posteriorMean (Function.update x j z) =
      M.posteriorMean (Function.update x j base) +
        M.signalWeight j * (z - base) := by
  classical
  have hsum (t : ℝ) :
      (∑ i : ι, M.signalWeight i * Function.update x j t i) =
        M.signalWeight j * t +
          ∑ i : ι, if i = j then 0 else M.signalWeight i * x i := by
    calc
      (∑ i : ι, M.signalWeight i * Function.update x j t i) =
          ∑ i : ι,
            ((if i = j then M.signalWeight i * t else 0) +
              if i = j then 0 else M.signalWeight i * x i) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : i = j <;> simp [Function.update, h]
      _ = (∑ i : ι, if i = j then M.signalWeight i * t else 0) +
            ∑ i : ι, if i = j then 0 else M.signalWeight i * x i := by
        rw [Finset.sum_add_distrib]
      _ = M.signalWeight j * t +
            ∑ i : ι, if i = j then 0 else M.signalWeight i * x i := by
        rw [Finset.sum_ite_eq']
        simp
  rw [M.posteriorMean_eq_weighted_sum, M.posteriorMean_eq_weighted_sum,
    hsum z, hsum base]
  ring

theorem posteriorMean_update_eq_base_add_weight_mul [DecidableEq ι]
    (M : GaussianSignalFamily ι) (x : ι → ℝ) (j : ι) (z : ℝ) :
    M.posteriorMean (Function.update x j z) =
      M.posteriorMean (Function.update x j 0) + M.signalWeight j * z := by
  simpa using M.posteriorMean_update_eq_base_add_weight_mul_sub x j 0 z

/-
Coordinate-threshold form for finite Gaussian posterior means: after fixing
all other signals, clearing a posterior-mean threshold is equivalent to the
selected signal exceeding the induced affine cutoff.
-/
end GaussianSignalFamily

/-
Finite Gaussian signal family with nonzero signal-specific noise means.

The observed signal has the source-paper form `x i = q + noiseMean i + error i`;
posterior formulas are delegated to `GaussianSignalFamily` after centering each
coordinate by `noiseMean i`.
-/
structure GaussianOffsetSignalFamily (ι : Type*) [Fintype ι] where
  priorMean : ℝ
  priorVar : ℝ
  noiseMean : ι → ℝ
  noiseVar : ι → ℝ
  priorVar_pos : 0 < priorVar
  noiseVar_pos : ∀ i, 0 < noiseVar i

namespace GaussianOffsetSignalFamily

variable {ι : Type*} [Fintype ι]

def centeredFamily (M : GaussianOffsetSignalFamily ι) :
    GaussianSignalFamily ι where
  priorMean := M.priorMean
  priorVar := M.priorVar
  noiseVar := M.noiseVar
  priorVar_pos := M.priorVar_pos
  noiseVar_pos := M.noiseVar_pos

def centeredSignal (M : GaussianOffsetSignalFamily ι)
    (x : ι → ℝ) (i : ι) : ℝ :=
  x i - M.noiseMean i

def posteriorMean (M : GaussianOffsetSignalFamily ι)
    (x : ι → ℝ) : ℝ :=
  M.centeredFamily.posteriorMean (M.centeredSignal x)

theorem posteriorMean_eq_weighted_sum
    (M : GaussianOffsetSignalFamily ι) (x : ι → ℝ) :
    M.posteriorMean x =
      M.centeredFamily.priorWeight * M.priorMean +
        ∑ i : ι,
          M.centeredFamily.signalWeight i *
            (x i - M.noiseMean i) := by
  rw [posteriorMean, GaussianSignalFamily.posteriorMean_eq_weighted_sum]
  rfl

/-
Posterior mean for offset signals in the source-paper precision-weighted form.
Each raw signal is centered by its group-specific noise mean.
-/
theorem posteriorMean_lt_of_pointwise_le_exists_lt
    (M : GaussianOffsetSignalFamily ι) {x y : ι → ℝ}
    (hxy : ∀ i, x i ≤ y i) (j : ι) (hstrict : x j < y j) :
    M.posteriorMean x < M.posteriorMean y := by
  rw [posteriorMean, posteriorMean]
  exact M.centeredFamily.posteriorMean_lt_of_pointwise_le_exists_lt
    (fun i => sub_le_sub_right (hxy i) (M.noiseMean i)) j
    (sub_lt_sub_right hstrict (M.noiseMean j))

/- Holding all other raw signals fixed, the offset-family posterior mean is
strictly increasing in any one raw signal. -/
theorem posteriorMean_update_strictMono [DecidableEq ι]
    (M : GaussianOffsetSignalFamily ι) (x : ι → ℝ) (j : ι) :
    StrictMono (fun z : ℝ => M.posteriorMean (Function.update x j z)) := by
  intro a b hab
  refine M.posteriorMean_lt_of_pointwise_le_exists_lt ?_ j ?_
  · intro i
    by_cases h : i = j
    · subst h
      simp [Function.update, hab.le]
    · simp [Function.update, h]
  · simp [Function.update, hab]

/-
Holding all other raw signals fixed, the offset-family posterior mean is an
affine function of the selected raw signal.
-/
theorem posteriorMean_update_eq_base_add_weight_mul_sub [DecidableEq ι]
    (M : GaussianOffsetSignalFamily ι) (x : ι → ℝ) (j : ι) (base z : ℝ) :
    M.posteriorMean (Function.update x j z) =
      M.posteriorMean (Function.update x j base) +
        M.centeredFamily.signalWeight j * (z - base) := by
  have hcenter (t : ℝ) :
      M.centeredSignal (Function.update x j t) =
        Function.update (M.centeredSignal x) j (t - M.noiseMean j) := by
    ext i
    by_cases h : i = j
    · subst h
      simp [centeredSignal, Function.update]
    · simp [centeredSignal, Function.update, h]
  rw [posteriorMean, posteriorMean, hcenter z, hcenter base,
    M.centeredFamily.posteriorMean_update_eq_base_add_weight_mul_sub
      (M.centeredSignal x) j (base - M.noiseMean j) (z - M.noiseMean j)]
  ring

theorem posteriorMean_update_eq_base_add_weight_mul [DecidableEq ι]
    (M : GaussianOffsetSignalFamily ι) (x : ι → ℝ) (j : ι) (z : ℝ) :
    M.posteriorMean (Function.update x j z) =
      M.posteriorMean (Function.update x j 0) +
        M.centeredFamily.signalWeight j * z := by
  simpa using M.posteriorMean_update_eq_base_add_weight_mul_sub x j 0 z

/-
Coordinate-threshold form for offset Gaussian posterior means: after fixing
all other raw signals, clearing a posterior-mean threshold is equivalent to the
selected raw signal exceeding the induced affine cutoff.
-/
end GaussianOffsetSignalFamily

/-
Reusable certificate for normal-density/tail analytic facts.

GLM/LG-style papers can use this as the boundary between algebraic Gaussian
formalization and the hard analytic facts about inverse Mills ratios or hazard
rates.
-/
namespace GaussianHazardCertificate

section Mixture

variable {γ : Type*} [Fintype γ]

end Mixture

end GaussianHazardCertificate

end

end Probability
end EconCSLib
