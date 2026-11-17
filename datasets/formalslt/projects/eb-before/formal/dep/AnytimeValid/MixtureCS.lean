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

end

end FormalSLT.AnytimeValid
