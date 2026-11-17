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
Theorem 3.1 report-required crossing step: continuity plus opposite endpoint
comparisons produce a finite skill cutoff where taking/reporting is indifferent
and taking/reporting is optimal exactly above the cutoff skill.
-/
theorem paper_interface_theorem3_1_report_required_threshold_equilibrium_exists_of_crossing
    {takeEstimate noTakeEstimateAtCutoff : ℝ → ℝ} {low high : ℝ}
    (hcontTake : ContinuousOn takeEstimate (Set.Icc low high))
    (hcontNoTake :
      ContinuousOn noTakeEstimateAtCutoff (Set.Icc low high))
    (hmonoTake : StrictMono takeEstimate)
    (hlow_high : low < high)
    (hleft : takeEstimate low < noTakeEstimateAtCutoff low)
    (hright : noTakeEstimateAtCutoff high < takeEstimate high) :
    ∃ qBar : ℝ,
      qBar ∈ Set.Ioo low high ∧
        noTakeEstimateAtCutoff qBar = takeEstimate qBar ∧
          (∀ skill : ℝ,
            noTakeEstimateAtCutoff qBar ≤ takeEstimate skill ↔
              qBar ≤ skill) ∧
            (∀ skill : ℝ,
              takeEstimate skill < noTakeEstimateAtCutoff qBar ↔
                skill < qBar) := sorry

end

end LG21TestOptionalPolicies
