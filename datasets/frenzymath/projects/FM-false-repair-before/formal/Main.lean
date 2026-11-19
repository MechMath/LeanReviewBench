import Mathlib
open MeasureTheory Measure Metric Set Module Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace MorganTianLib
section

noncomputable def snK (k r : ℝ) : ℝ :=
  if k = 0 then r else Real.sinh (Real.sqrt k * r) / Real.sqrt k
end
end MorganTianLib
namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
def modelDensity (k : ℝ) (x : E) : ℝ :=
  if ‖x‖ = 0 then 1 else (snK k ‖x‖ / ‖x‖) ^ (finrank ℝ E - 1)
end
end MorganTianLib
namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
def modelBallVolume (k : ℝ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in ball (0 : E) r,
    ENNReal.ofReal (modelDensity (E := E) k x) ∂μ
end
end MorganTianLib
namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [Nontrivial E] [FiniteDimensional ℝ E]
variable {ℛ 𝒥 𝒥' : ℝ → E →L[ℝ] E} {b C : ℝ}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]
theorem model_polar_volume_identity (k r : ℝ) :
    modelBallVolume μ k r =
      μ.toSphere univ * ∫⁻ t in Ioo (0 : ℝ) r,
        ENNReal.ofReal (snK k t ^ (finrank ℝ E - 1)) := by sorry
end
end MorganTianLib
end
