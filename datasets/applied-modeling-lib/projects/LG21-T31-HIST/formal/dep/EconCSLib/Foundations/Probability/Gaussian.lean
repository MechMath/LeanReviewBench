import Mathlib

open scoped BigOperators

namespace EconCSLib

namespace Probability

noncomputable section

structure GaussianVarianceLaw where
  mean : ℝ
  variance : ℝ
  variance_pos : 0 < variance

structure GaussianScaleLaw where
  mean : ℝ
  scale : ℝ
  scale_pos : 0 < scale

namespace GaussianScaleLaw

def affineImage (L : GaussianScaleLaw) (a b : ℝ) (hb : 0 < b) :
    GaussianScaleLaw where
  mean := a + b * L.mean
  scale := b * L.scale
  scale_pos := mul_pos hb L.scale_pos

end GaussianScaleLaw

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

section Mixture

variable {γ : Type*} [Fintype γ]

namespace MixtureThresholdCertificate

end MixtureThresholdCertificate

end Mixture

end StandardGaussianCDFAPI

namespace GaussianLowerTailMeanCertificate

end GaussianLowerTailMeanCertificate

namespace GaussianVarianceLaw

def affineImage (L : GaussianVarianceLaw) (a b : ℝ) (hb : b ≠ 0) :
    GaussianVarianceLaw where
  mean := a + b * L.mean
  variance := b ^ 2 * L.variance
  variance_pos := sorry

end GaussianVarianceLaw

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

def signalWeight (M : GaussianPriorSignal) : ℝ :=
  M.priorVar / (M.priorVar + M.noiseVar)

def posteriorMean (M : GaussianPriorSignal) (x : ℝ) : ℝ :=
  M.posteriorVariance *
    (M.priorPrecision * M.priorMean + M.noisePrecision * x)

theorem signalWeight_pos (M : GaussianPriorSignal) :
    0 < M.signalWeight := sorry

end GaussianPriorSignal

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

def posteriorPrecision (M : GaussianSignalFamily ι) : ℝ :=
  M.priorPrecision + ∑ i : ι, M.signalPrecision i

def posteriorVariance (M : GaussianSignalFamily ι) : ℝ :=
  M.posteriorPrecision⁻¹

def signalWeight (M : GaussianSignalFamily ι) (i : ι) : ℝ :=
  M.posteriorVariance * M.signalPrecision i

def posteriorMean (M : GaussianSignalFamily ι) (x : ι → ℝ) : ℝ :=
  M.posteriorVariance *
    (M.priorPrecision * M.priorMean +
      ∑ i : ι, M.signalPrecision i * x i)

theorem signalWeight_pos (M : GaussianSignalFamily ι) (i : ι) :
    0 < M.signalWeight i := sorry

end GaussianSignalFamily

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

end GaussianOffsetSignalFamily

namespace GaussianHazardCertificate

section Mixture

variable {γ : Type*} [Fintype γ]

end Mixture

end GaussianHazardCertificate

end

end Probability

end EconCSLib
