import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Notation
import Mathlib.Probability.Process.HittingTime
import Mathlib.Tactic
import dep.AnytimeValid.SubGaussianCS

open MeasureTheory ProbabilityTheory

open scoped BigOperators

namespace FormalSLT.AnytimeValid

noncomputable section

/-- Prior mixture of the fixed-tilt sub-Gamma exponential processes. -/
def mixtureExponentialProcess {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (sigma2 b : ℝ) (ρ : Measure ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∫ lam, subGammaExponentialProcess X sigma2 b lam n ω ∂ρ

/-- Continuous uniform prior on a compact tilt interval. -/
def uniformTiltPrior (lam0 lam1 : ℝ) : Measure ℝ :=
  volume[|Set.Icc lam0 lam1]

/--
The mixture confidence sequence for the continuous uniform tilt prior, with **no free
measurability or integrability hypotheses**. From the conditional sub-Gamma increment model on `X`
(adapted, bounded `|X_k| ≤ b`, conditionally centered `μ[X_k | F_k] = 0`, conditional second moment
`μ[X_k² | F_k] ≤ σ²`) and an admissible compact tilt interval `[lam0, lam1] ⊆ (0, 3/b)`, the
prior-mixture exponential process is an anytime-valid confidence sequence:

`μ.real {ω | ∃ n > 0, 1/δ ≤ ∫ lam, M_λ(n, ω) ∂Unif[lam0,lam1]} ≤ δ`.

Every measurability / integrability obligation of
`atTop_time_uniform_confidence_sequence_subGamma_mixture` is discharged internally for the concrete
uniform prior: joint measurability from `hX_meas`, the four product-integrability conditions from the
process bound `M ≤ exp (lam1 · n · b)` via `Integrable.of_bound`, and both adaptedness conditions
from `hX_adapted`.
-/
theorem mixture_confidence_sequence_uniformPrior
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b delta lam0 lam1 : ℝ}
    (hδ : 0 < delta)
    (hb : 0 < b) (hσ : 0 ≤ sigma2)
    (hlam0 : 0 < lam0) (h01 : lam0 < lam1) (hlam1 : lam1 < 3 / b)
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (hX_adapted : StronglyAdapted ℱ X)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    μ.real {ω | ∃ n : ℕ, 0 < n ∧
      (1 / delta) ≤ mixtureExponentialProcess X sigma2 b (uniformTiltPrior lam0 lam1) n ω}
        ≤ delta := sorry

end

end FormalSLT.AnytimeValid
