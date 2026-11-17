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
import dep.AnytimeValid.MixtureCS
import dep.AnytimeValid.SubGaussianCS

open MeasureTheory ProbabilityTheory

open scoped BigOperators

namespace FormalSLT.AnytimeValid

noncomputable section

/-- Bernstein cumulant multiplier for a predictable variance proxy. -/
def empiricalBernsteinCgf (b lam : ℝ) : ℝ :=
  lam ^ 2 / (2 * (1 - b * lam / 3))

/-- Running predictable variance proxy. -/
def runningVarianceProxy {Ω : Type*} (V : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Finset.sum (Finset.range n) fun i => V i ω

/-- Fixed-tilt empirical-Bernstein exponential process. -/
def empiricalBernsteinExponentialProcess {Ω : Type*}
    (X V : ℕ → Ω → ℝ) (b lam : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp
    (lam * runningSum X n ω - empiricalBernsteinCgf b lam * runningVarianceProxy V n ω)

/-- Prior mixture of empirical-Bernstein exponential processes. -/
def empiricalBernsteinMixtureProcess {Ω : Type*} [MeasurableSpace Ω]
    (X V : ℕ → Ω → ℝ) (b : ℝ) (ρ : Measure ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∫ lam, empiricalBernsteinExponentialProcess X V b lam n ω ∂ρ

/--
Uniform-prior empirical-Bernstein mixture CS with product measurability and
integrability discharged from the bounded, nonnegative predictable-proxy model.
-/
theorem empiricalBernstein_confidence_sequence_uniformPrior
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X V : ℕ → Ω → ℝ} {b delta lam0 lam1 : ℝ}
    (hδ : 0 < delta)
    (hb : 0 < b) (hlam0 : 0 < lam0) (h01 : lam0 < lam1) (hlam1 : lam1 < 3 / b)
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (hV_meas : ∀ k, Measurable (V k))
    (hX_adapted : StronglyAdapted ℱ X) (hV_adapted : StronglyAdapted ℱ V)
    (hV_nonneg : ∀ k, 0 ≤ V k)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] V k) :
    μ.real {ω | ∃ n : ℕ, 0 < n ∧
      (1 / delta) ≤ empiricalBernsteinMixtureProcess X V b (uniformTiltPrior lam0 lam1) n ω}
        ≤ delta := sorry

end

end FormalSLT.AnytimeValid
