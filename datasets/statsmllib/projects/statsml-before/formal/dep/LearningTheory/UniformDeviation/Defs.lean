import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Notation

noncomputable section

universe u v w

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal

variable {Ω : Type u} [MeasurableSpace Ω] {ι : Type v} {𝒳 : Type w}

/-- The largest absolute difference between empirical and population expectations over a function
class. -/
def uniformDeviation (n : ℕ) (f : ι → 𝒳 → ℝ) (μ : Measure Ω) (X : Ω → 𝒳)
    (S : Fin n → 𝒳) : ℝ :=
  ⨆ i, |(n : ℝ)⁻¹ * ∑ k : Fin n, f i (S k) - μ[fun ω' ↦ f i (X ω')]|

end
