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

namespace LG21TestOptionalPolicies

noncomputable section



/--
Theorem 3.1 optional-reporting crossing step: continuity plus opposite endpoint
comparisons produce a finite cutoff where reporting at the cutoff is indifferent
and reporting is optimal exactly above the cutoff score.
-/
theorem paper_interface_theorem3_1_optional_reporting_threshold_equilibrium_exists_of_crossing
    {reportedEstimate noReportEstimateAtCutoff : ℝ → ℝ} {low high : ℝ}
    (hcontReported :
      ContinuousOn reportedEstimate (Set.Icc low high))
    (hcontNoReport :
      ContinuousOn noReportEstimateAtCutoff (Set.Icc low high))
    (hmonoReported : StrictMono reportedEstimate)
    (hlow_high : low < high)
    (hleft : reportedEstimate low < noReportEstimateAtCutoff low)
    (hright : noReportEstimateAtCutoff high < reportedEstimate high) :
    ∃ cutoff : ℝ,
      cutoff ∈ Set.Ioo low high ∧
        noReportEstimateAtCutoff cutoff = reportedEstimate cutoff ∧
          (∀ score : ℝ,
            noReportEstimateAtCutoff cutoff ≤ reportedEstimate score ↔
              cutoff ≤ score) ∧
            (∀ score : ℝ,
              reportedEstimate score < noReportEstimateAtCutoff cutoff ↔
                score < cutoff) := sorry

end

end LG21TestOptionalPolicies
