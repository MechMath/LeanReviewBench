import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace EconCSLib

namespace Probability

noncomputable section

/-- A Gaussian law represented by mean and variance. -/
structure GaussianVarianceLaw where
  mean : ℝ
  variance : ℝ
  variance_pos : 0 < variance

/-- A Gaussian location-scale law represented by mean and positive scale. -/
structure GaussianScaleLaw where
  mean : ℝ
  scale : ℝ
  scale_pos : 0 < scale

namespace GaussianScaleLaw

/-- Standardize a value relative to a Gaussian location-scale law. -/
def standardize (L : GaussianScaleLaw) (x : ℝ) : ℝ :=
  (x - L.mean) / L.scale

end GaussianScaleLaw

/--
Abstract standard-normal CDF/density API.

Analytic papers can instantiate this once a concrete normal CDF/density library
is available. Until then, paper-specific Gaussian proofs can state exactly
which normal facts they require without hiding them in theorem conclusions.
-/
structure StandardGaussianCDFAPI where
  cdf : ℝ → ℝ
  density : ℝ → ℝ
  cdf_mono : Monotone cdf
  cdf_strictMono : StrictMono cdf
  cdf_zero_eq_half : cdf 0 = (1 / 2 : ℝ)
  density_nonneg : ∀ z, 0 ≤ density z
  cdf_nonneg : ∀ z, 0 ≤ cdf z
  cdf_le_one : ∀ z, cdf z ≤ 1

namespace StandardGaussianCDFAPI

/-- Normal CDF for an arbitrary location-scale law by standardization. -/
def normalCDF (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (x : ℝ) : ℝ :=
  api.cdf (L.standardize x)

/-- Normal upper tail for an arbitrary location-scale law. -/
def normalTail (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (x : ℝ) : ℝ :=
  1 - api.normalCDF L x

/-- Pass probability above a threshold for a Gaussian location-scale law. -/
def thresholdPassProb (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (threshold : ℝ) : ℝ :=
  api.normalTail L threshold

section Mixture

variable {γ : Type*} [Fintype γ]

/-- Weighted admission mass above a common threshold for finitely many Gaussian groups. -/
def mixtureTailMass (api : StandardGaussianCDFAPI)
    (weight : γ → ℝ) (law : γ → GaussianScaleLaw)
    (threshold : ℝ) : ℝ :=
  ∑ g : γ, weight g * api.thresholdPassProb (law g) threshold

/--
Certificate that a common Gaussian admission threshold realizes a target
capacity for a finite mixture of group score laws.
-/
structure MixtureThresholdCertificate
    (api : StandardGaussianCDFAPI) (γ : Type*) [Fintype γ] where
  weight : γ → ℝ
  law : γ → GaussianScaleLaw
  threshold : ℝ
  capacity : ℝ
  weight_nonneg : ∀ g, 0 ≤ weight g
  capacity_eq : api.mixtureTailMass weight law threshold = capacity

namespace MixtureThresholdCertificate

end MixtureThresholdCertificate

end Mixture

end StandardGaussianCDFAPI

namespace GaussianVarianceLaw

end GaussianVarianceLaw

/--
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

end GaussianPriorSignal

/-- Conjugate Gaussian model with a finite family of noisy signals. -/
structure GaussianSignalFamily (ι : Type*) [Fintype ι] where
  priorMean : ℝ
  priorVar : ℝ
  noiseVar : ι → ℝ
  priorVar_pos : 0 < priorVar
  noiseVar_pos : ∀ i, 0 < noiseVar i

namespace GaussianSignalFamily

variable {ι : Type*} [Fintype ι]

end GaussianSignalFamily

/--
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

end GaussianOffsetSignalFamily

/--
Reusable certificate for normal-density/tail analytic facts.

GLM/LG-style papers can use this as the boundary between algebraic Gaussian
formalization and the hard analytic facts about inverse Mills ratios or hazard
rates.
-/
structure GaussianHazardCertificate where
  api : StandardGaussianCDFAPI
  hazard : ℝ → ℝ
  tail_pos : ∀ z, 0 < 1 - api.cdf z
  hazard_eq : ∀ z, hazard z = api.density z / (1 - api.cdf z)
  hazard_mono : Monotone hazard

namespace GaussianHazardCertificate

section Mixture

variable {γ : Type*} [Fintype γ]

end Mixture

end GaussianHazardCertificate

end

end Probability

end EconCSLib
