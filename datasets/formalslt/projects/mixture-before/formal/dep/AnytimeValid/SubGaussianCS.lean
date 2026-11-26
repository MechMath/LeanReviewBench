import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Notation
import Mathlib.Probability.Process.HittingTime
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory

open scoped BigOperators

namespace FormalSLT.AnytimeValid

noncomputable section

/-- Sub-Gamma cumulant proxy used by the fixed-`lambda` exponential process. -/
def subGammaCgf (sigma2 b lam : ℝ) : ℝ :=
  sigma2 * lam ^ 2 / (2 * (1 - b * lam / 3))

/-- Running sum `S_n = sum_{i < n} X_i`. -/
def runningSum {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Finset.sum (Finset.range n) fun i => X i ω

/-- Fixed-`lambda` sub-Gamma exponential process. -/
def subGammaExponentialProcess {Ω : Type*}
    (X : ℕ → Ω → ℝ) (sigma2 b lam : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (lam * runningSum X n ω - (n : ℝ) * subGammaCgf sigma2 b lam)

end

end FormalSLT.AnytimeValid
