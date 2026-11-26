import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import dep.GhostSample
import dep.Risk

namespace FormalSLT.OnlineToPAC

open Finset BigOperators

noncomputable section

/-- Finite bounded-loss data needed by the algebraic online-to-PAC conversion. -/
structure BoundedLossRegretConversionInput (T : ℕ) where
  lossBound : ℝ
  populationLoss : Fin T → ℝ
  empiricalLoss : Fin T → ℝ
  comparatorEmpiricalLoss : ℝ
  regretBound : ℝ
  deviationBound : ℝ

end

end FormalSLT.OnlineToPAC
