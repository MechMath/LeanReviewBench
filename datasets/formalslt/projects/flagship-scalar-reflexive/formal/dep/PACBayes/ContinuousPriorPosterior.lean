import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Tactic

namespace FormalSLT.PACBayes

open MeasureTheory

/-- Continuous-prior PAC-Bayes certificate data. -/
structure ContinuousPriorPosteriorSpec (Θ : Type*) [MeasurableSpace Θ] where
  prior : Measure Θ
  posterior : Measure Θ
  sampleSize : ℕ
  lossBound : ℝ
  empiricalRisk : ℝ
  populationRisk : ℝ
  varianceBound : ℝ
  klBound : ℝ
  confidencePenalty : ℝ
  complexityBound : ℝ
  pacPenalty : ℝ

end FormalSLT.PACBayes
