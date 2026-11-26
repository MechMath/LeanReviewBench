import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.Linarith

namespace FormalSLT.PACBayes

open Finset Real BigOperators







noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The square-root McAllester penalty for a fixed complexity budget. -/
def mcAllesterPenalty (n : ℕ) (complexityBound : ℝ) : ℝ :=
  Real.sqrt (complexityBound / (2 * (n : ℝ)))

end

end FormalSLT.PACBayes
