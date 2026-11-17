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
Theorem 3.1 optional-reporting source witness from the paper's crossing
argument, applied independently at every base profile.
-/
theorem paper_interface_theorem3_1_optional_reporting_source_witness_of_base_crossings
    {Base : Type*} [Nonempty Base]
    (reportedEstimate noReportEstimateAtCutoff : Base → ℝ → ℝ)
    (low high : Base → ℝ)
    (hcontReported :
      ∀ base, ContinuousOn (reportedEstimate base)
        (Set.Icc (low base) (high base)))
    (hcontNoReport :
      ∀ base, ContinuousOn (noReportEstimateAtCutoff base)
        (Set.Icc (low base) (high base)))
    (hmonoReported : ∀ base, StrictMono (reportedEstimate base))
    (hlow_high : ∀ base, low base < high base)
    (hleft :
      ∀ base, reportedEstimate base (low base) <
        noReportEstimateAtCutoff base (low base))
    (hright :
      ∀ base, noReportEstimateAtCutoff base (high base) <
        reportedEstimate base (high base)) :
    ∃ W : LG21OptionalReportingStrategicWithholdingSourceWitness Base,
      ∃ reportCutoff : Base → ℝ,
        (∀ base, reportCutoff base ∈ Set.Ioo (low base) (high base)) ∧
          (∀ base,
            noReportEstimateAtCutoff base (reportCutoff base) =
              reportedEstimate base (reportCutoff base)) ∧
            (∀ base score,
              W.reports base score ↔
                noReportEstimateAtCutoff base (reportCutoff base) ≤
                  reportedEstimate base score) ∧
              (∀ base skill, W.takes base skill) ∧
                (∀ base, ∃ cutoff : ℝ,
                  ∀ score : ℝ, W.reports base score ↔ cutoff ≤ score) := sorry

end

end LG21TestOptionalPolicies
