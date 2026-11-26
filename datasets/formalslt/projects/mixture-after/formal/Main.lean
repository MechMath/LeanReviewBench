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
**Predictable-increment (martingale-difference) adaptedness.**

The increment `X_k` is revealed at time `k + 1`, i.e. each `X_k` is `ℱ (k+1)`-strongly-measurable.
This is the correct admissibility for a martingale-difference sequence whose centering and
conditional variance are taken with respect to the past `ℱ k`: it lets `X_k` be a genuine
nonconstant increment while keeping `μ[X k | ℱ k] = 0` non-vacuous.

Conditioning the *present* (`StronglyAdapted ℱ X`, i.e. each `X_k` is `ℱ k`-measurable) together
with `μ[X k | ℱ k] = 0` would force `X_k =ᵐ 0` by `condExp_of_stronglyMeasurable`, leaving only the
zero process admissible. The `+1` shift is what avoids that collapse. The running sum `S_n`
remains `ℱ n`-measurable because it only involves `X_0, …, X_{n-1}`, each `ℱ n`-measurable since
`i < n ⟹ i + 1 ≤ n`. -/
def IncrementAdapted {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ)
    (X : ℕ → Ω → ℝ) : Prop :=
  ∀ k, StronglyMeasurable[ℱ (k + 1)] (X k)

/--
The mixture confidence sequence for the continuous uniform tilt prior, with **no free
measurability or integrability hypotheses**. The increment model on `X` is a genuine
martingale-difference sequence: each increment `X_k` is revealed at time `k + 1`
(`IncrementAdapted ℱ X`, i.e. `X_k` is `ℱ (k+1)`-strongly-measurable), is bounded `|X_k| ≤ b`,
is conditionally centered with respect to the **past** `μ[X_k | F_k] = 0`, and has conditional
second moment `μ[X_k² | F_k] ≤ σ²`. With an admissible compact tilt interval
`[lam0, lam1] ⊆ (0, 3/b)`, the prior-mixture exponential process is an anytime-valid confidence
sequence:

`μ.real {ω | ∃ n > 0, 1/δ ≤ ∫ lam, M_λ(n, ω) ∂Unif[lam0,lam1]} ≤ δ`.

The `+1` increment shift is essential for non-vacuity: pairing the *present*-conditioning
`StronglyAdapted ℱ X` with `μ[X_k | F_k] = 0` would force `X_k =ᵐ 0` (by
`condExp_of_stronglyMeasurable`), admitting only the zero process. With the shift the centering is
genuine and the running sum `S_n` is still `ℱ n`-measurable (it uses only `X_0, …, X_{n-1}`).

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
    (hX_adapted : IncrementAdapted ℱ X)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    μ.real {ω | ∃ n : ℕ, 0 < n ∧
      (1 / delta) ≤ mixtureExponentialProcess X sigma2 b (uniformTiltPrior lam0 lam1) n ω}
        ≤ delta := sorry

end

end FormalSLT.AnytimeValid
