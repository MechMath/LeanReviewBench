import Mathlib

open MeasureTheory Measure Metric Set Module Filter

open scoped ENNReal NNReal Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

noncomputable def snK (k r : ℝ) : ℝ :=
  if k = 0 then r else Real.sinh (Real.sqrt k * r) / Real.sqrt k

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

def expBallVolume (ρ : E → ℝ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in ball (0 : E) r, ENNReal.ofReal (ρ x) ∂μ

def modelBallVolume (k : ℝ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in ball (0 : E) r,
    ENNReal.ofReal ((snK k ‖x‖ / ‖x‖) ^ (finrank ℝ E - 1)) ∂μ

def polarBallDensity (ρ : E → ℝ) (ω : E) (t : ℝ) : ℝ :=
  t ^ (finrank ℝ E - 1) * ρ (t • ω)

theorem bishop_gromov_ball {ρ : E → ℝ} (hρmeas : Measurable ρ) (hρ : ∀ x, 0 ≤ ρ x)
    {k R : ℝ} (hk : 0 ≤ k)
    (hanti : ∀ ω ∈ sphere (0 : E) 1,
      AntitoneOn (fun t => polarBallDensity ρ ω t / snK k t ^ (finrank ℝ E - 1)) (Ioo 0 R))
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h12 : r₁ ≤ r₂) (hr₂ : r₂ < R) :
    expBallVolume μ ρ r₂ * modelBallVolume μ k r₁
      ≤ expBallVolume μ ρ r₁ * modelBallVolume μ k r₂ := by
  sorry

theorem bishop_gromov_ball_ratio {ρ : E → ℝ} (hρmeas : Measurable ρ) (hρ : ∀ x, 0 ≤ ρ x)
    {k R : ℝ} (hk : 0 ≤ k)
    (hanti : ∀ ω ∈ sphere (0 : E) 1,
      AntitoneOn (fun t => polarBallDensity ρ ω t / snK k t ^ (finrank ℝ E - 1)) (Ioo 0 R)) :
    AntitoneOn (fun r => expBallVolume μ ρ r / modelBallVolume μ k r) (Ioo 0 R) := by
  sorry

end MorganTianLib
