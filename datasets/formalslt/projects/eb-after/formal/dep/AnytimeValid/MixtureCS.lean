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

end

end FormalSLT.AnytimeValid
