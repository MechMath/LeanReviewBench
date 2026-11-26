import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import dep.EconCSLib.Foundations.Probability.Gaussian
import dep.LG21TestOptionalPolicies.MainTheorems

namespace LG21TestOptionalPolicies

noncomputable section

open EconCSLib.Probability

/--
Theorem 3.1 report-required source witness from the paper's crossing argument,
applied independently at every base profile.
-/
theorem paper_interface_theorem3_1_report_required_source_witness_of_base_crossings
    {Base : Type*} [Nonempty Base]
    (takeEstimate noTakeEstimateAtCutoff : Base → ℝ → ℝ)
    (low high : Base → ℝ)
    (hcontTake :
      ∀ base, ContinuousOn (takeEstimate base)
        (Set.Icc (low base) (high base)))
    (hcontNoTake :
      ∀ base, ContinuousOn (noTakeEstimateAtCutoff base)
        (Set.Icc (low base) (high base)))
    (hmonoTake : ∀ base, StrictMono (takeEstimate base))
    (hlow_high : ∀ base, low base < high base)
    (hleft :
      ∀ base, takeEstimate base (low base) <
        noTakeEstimateAtCutoff base (low base))
    (hright :
      ∀ base, noTakeEstimateAtCutoff base (high base) <
        takeEstimate base (high base)) :
    ∃ W : LG21ReportRequiredStrategicWithholdingSourceWitness Base,
      ∃ takeCutoff : Base → ℝ,
        (∀ base, takeCutoff base ∈ Set.Ioo (low base) (high base)) ∧
          (∀ base,
            noTakeEstimateAtCutoff base (takeCutoff base) =
              takeEstimate base (takeCutoff base)) ∧
            (∀ base skill,
              W.takes base skill ↔
                noTakeEstimateAtCutoff base (takeCutoff base) ≤
                  takeEstimate base skill) ∧
              (∀ base, ∃ qBar : ℝ,
                ∀ skill : ℝ, W.takes base skill ↔ qBar ≤ skill) := sorry

end

end LG21TestOptionalPolicies
