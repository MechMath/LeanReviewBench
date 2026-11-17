import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

namespace FormalSLT.PACBayes

open MeasureTheory

open Finset Real BigOperators

noncomputable section

/-- Parameter space for a `d`-dimensional real Gaussian. -/
abbrev GaussianParameterSpace (d : ℕ) := Fin d → ℝ

/-- Diagonal finite-dimensional Gaussian parameters. -/
structure DiagonalGaussianParams (d : ℕ) where
  mean : GaussianParameterSpace d
  variance : Fin d → ℝ
  variance_pos : ∀ i, 0 < variance i

/-- Spherical finite-dimensional Gaussian parameters. -/
structure SphericalGaussianParams (d : ℕ) where
  mean : GaussianParameterSpace d
  variance : ℝ
  variance_pos : 0 < variance

namespace SphericalGaussianParams

/-- Convert a spherical Gaussian to a diagonal Gaussian with constant variance. -/
def toDiagonal {d : ℕ} (params : SphericalGaussianParams d) :
    DiagonalGaussianParams d where
  mean := params.mean
  variance := fun _ => params.variance
  variance_pos := fun _ => params.variance_pos

end SphericalGaussianParams

/-- One-dimensional Gaussian density factor. -/
def gaussianCoordinateDensity (mean variance x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * variance))⁻¹ *
    Real.exp (-((x - mean) ^ (2 : Nat)) / (2 * variance))

/-- Product density for a diagonal Gaussian on `Fin d → ℝ`. -/
def diagonalGaussianDensity {d : ℕ}
    (params : DiagonalGaussianParams d) (x : GaussianParameterSpace d) : ℝ :=
  ∏ i, gaussianCoordinateDensity (params.mean i) (params.variance i) (x i)

/-- ENNReal-valued density used to construct the Gaussian measure. -/
def diagonalGaussianENNRealDensity {d : ℕ}
    (params : DiagonalGaussianParams d) (x : GaussianParameterSpace d) : ENNReal :=
  ENNReal.ofReal (diagonalGaussianDensity params x)

/-- Diagonal Gaussian measure on `Fin d → ℝ`, represented by its Lebesgue density. -/
def diagonalGaussianMeasure {d : ℕ}
    (params : DiagonalGaussianParams d) : Measure (GaussianParameterSpace d) :=
  volume.withDensity (diagonalGaussianENNRealDensity params)

/-- Spherical Gaussian measure on `Fin d → ℝ`. -/
def sphericalGaussianMeasure {d : ℕ}
    (params : SphericalGaussianParams d) : Measure (GaussianParameterSpace d) :=
  diagonalGaussianMeasure params.toDiagonal

end

end FormalSLT.PACBayes
