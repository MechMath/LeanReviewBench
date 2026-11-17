import Mathlib
import dep.GCG24UserItemFairness.OpposingTypes

namespace GCG24UserItemFairness
namespace ReductionWitness

/-
Symmetric item-fairness reduction theorem.

The item-fairness values attainable by type-symmetric user-level policies are
exactly the values attainable by the reduced type-level problem.
-/
end ReductionWitness

namespace RecommendationModel

/-
Appendix C, Lemma 1: under the paper's strictly positive utility assumption,
the optimal minimum item fairness value is strictly positive.
-/
end RecommendationModel

namespace RecommendationModel.SymmetricData

/-
Proposition 2, part 1: `S_symm` satisfies the paper's symmetric-optimum
existence condition.

Given any optimum for the maximal item-fairness problem, averaging the policy
inside each equal-utility user type produces an optimum in `S_symm`.
-/
end RecommendationModel.SymmetricData

namespace OpposingTypes

/-
Appendix D, Lemma 9, scalar monotonicity in `α`.

For a fixed opposing item pair with positive utilities, the paper's
`q_j(α)` strictly increases as the mass `α` on the first type increases.
-/
theorem paper_theorem3_price_decreases_firstHalf_center_of_reduction
    {m n : ℕ} [NeZero m] [NeZero n]
    (R R' : ReductionWitness m n 2)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (reps' : UserTypeAssignment.TypeRepresentatives R'.data.types)
    {alpha alpha' : ℝ} {v : Item n → ℝ} {c : Item n}
    (hred : R.reduced = twoTypeReducedModel alpha v)
    (hred' : R'.reduced = twoTypeReducedModel alpha' v)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hNonneg : R.data.model.Nonnegative)
    (hRow : R.data.model.RowHasPositiveItem)
    (hNonneg' : R'.data.model.Nonnegative)
    (hRow' : R'.data.model.RowHasPositiveItem) :
    RecommendationModel.priceOfFairness R'.data.model ≤
      RecommendationModel.priceOfFairness R.data.model := by
  let ρred : TypePolicy 2 n :=
    problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos
  let ρred' : TypePolicy 2 n :=
    problem6FirstClosedPolicy alpha' v halpha0' halpha1' hpos
  have hReducedFeas :
      TypeWeightedRecommendationModel.feasibleAtLevel R.reduced 1 ρred := by
    rw [hred]
    exact problem6FirstClosedPolicy_feasibleAtLevel_one
      halpha0 halpha1 hpos hdec
  have hReducedFeas' :
      TypeWeightedRecommendationModel.feasibleAtLevel R'.reduced 1 ρred' := by
    rw [hred']
    exact problem6FirstClosedPolicy_feasibleAtLevel_one
      halpha0' halpha1' hpos hdec
  have hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel
        R.data.model 1).Nonempty := by
    refine ⟨RecommendationModel.userFairness R.data.model
      (R.liftedPolicy ρred), ?_⟩
    refine ⟨R.liftedPolicy ρred, ?_, rfl⟩
    unfold RecommendationModel.feasibleAtLevel
    rw [R.optimalItemFairness_eq_reduced reps]
    rw [R.itemFairness_liftedPolicy_eq_itemFairness ρred]
    exact hReducedFeas
  have hOrigNonempty' :
      (RecommendationModel.attainableUserFairnessAtLevel
        R'.data.model 1).Nonempty := by
    refine ⟨RecommendationModel.userFairness R'.data.model
      (R'.liftedPolicy ρred'), ?_⟩
    refine ⟨R'.liftedPolicy ρred', ?_, rfl⟩
    unfold RecommendationModel.feasibleAtLevel
    rw [R'.optimalItemFairness_eq_reduced reps']
    rw [R'.itemFairness_liftedPolicy_eq_itemFairness ρred']
    exact hReducedFeas'
  have hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced 1).Nonempty := by
    refine ⟨TypeWeightedRecommendationModel.typeFairness R.reduced ρred, ?_⟩
    exact ⟨ρred, hReducedFeas, rfl⟩
  have hRedNonempty' :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R'.reduced 1).Nonempty := by
    refine ⟨TypeWeightedRecommendationModel.typeFairness R'.reduced ρred', ?_⟩
    exact ⟨ρred', hReducedFeas', rfl⟩
  have hUserEq :
      RecommendationModel.optimalUserFairnessAtLevel R.data.model 1 =
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          R.reduced 1 :=
    R.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
      reps hRow 1 hOrigNonempty hRedNonempty
  have hUserEq' :
      RecommendationModel.optimalUserFairnessAtLevel R'.data.model 1 =
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          R'.reduced 1 :=
    R'.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
      reps' hRow' 1 hOrigNonempty' hRedNonempty'
  have hred_mono :
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          R.reduced 1 ≤
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          R'.reduced 1 := by
    rw [hred, hred']
    exact theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_of_alpha_le
      halpha0 halpha1 halpha0' halpha1' halpha_le
      halpha_half halpha_half' hpos hdec hcenter_c
  have huser_mono :
      RecommendationModel.optimalUserFairnessAtLevel R.data.model 1 ≤
        RecommendationModel.optimalUserFairnessAtLevel R'.data.model 1 := by
    rw [hUserEq, hUserEq']
    exact hred_mono
  exact R.data.model.priceOfFairness_le_of_optimalUserFairnessAtLevel_one_le
    R'.data.model hNonneg hRow hNonneg' hRow' huser_mono

/-
Theorem 3 paper-facing price monotonicity, even-center first-half form. The two
original recommendation models are connected to the opposing two-type reduced
models by reduction witnesses; the first-closed reduced policy supplies the
`γ = 1` feasible witnesses needed on both the original and reduced sides.
-/
theorem paper_theorem3_price_decreases_firstHalf_succ_center_of_reduction
    {m n : ℕ} [NeZero m] [NeZero n]
    (R R' : ReductionWitness m n 2)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (reps' : UserTypeAssignment.TypeRepresentatives R'.data.types)
    {alpha alpha' : ℝ} {v : Item n → ℝ} {c : Item n}
    (hred : R.reduced = twoTypeReducedModel alpha v)
    (hred' : R'.reduced = twoTypeReducedModel alpha' v)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hNonneg : R.data.model.Nonnegative)
    (hRow : R.data.model.RowHasPositiveItem)
    (hNonneg' : R'.data.model.Nonnegative)
    (hRow' : R'.data.model.RowHasPositiveItem) :
    RecommendationModel.priceOfFairness R'.data.model ≤
      RecommendationModel.priceOfFairness R.data.model := by
  let ρred : TypePolicy 2 n :=
    problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos
  let ρred' : TypePolicy 2 n :=
    problem6FirstClosedPolicy alpha' v halpha0' halpha1' hpos
  have hReducedFeas :
      TypeWeightedRecommendationModel.feasibleAtLevel R.reduced 1 ρred := by
    rw [hred]
    exact problem6FirstClosedPolicy_feasibleAtLevel_one
      halpha0 halpha1 hpos hdec
  have hReducedFeas' :
      TypeWeightedRecommendationModel.feasibleAtLevel R'.reduced 1 ρred' := by
    rw [hred']
    exact problem6FirstClosedPolicy_feasibleAtLevel_one
      halpha0' halpha1' hpos hdec
  have hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel
        R.data.model 1).Nonempty := by
    refine ⟨RecommendationModel.userFairness R.data.model
      (R.liftedPolicy ρred), ?_⟩
    refine ⟨R.liftedPolicy ρred, ?_, rfl⟩
    unfold RecommendationModel.feasibleAtLevel
    rw [R.optimalItemFairness_eq_reduced reps]
    rw [R.itemFairness_liftedPolicy_eq_itemFairness ρred]
    exact hReducedFeas
  have hOrigNonempty' :
      (RecommendationModel.attainableUserFairnessAtLevel
        R'.data.model 1).Nonempty := by
    refine ⟨RecommendationModel.userFairness R'.data.model
      (R'.liftedPolicy ρred'), ?_⟩
    refine ⟨R'.liftedPolicy ρred', ?_, rfl⟩
    unfold RecommendationModel.feasibleAtLevel
    rw [R'.optimalItemFairness_eq_reduced reps']
    rw [R'.itemFairness_liftedPolicy_eq_itemFairness ρred']
    exact hReducedFeas'
  have hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced 1).Nonempty := by
    refine ⟨TypeWeightedRecommendationModel.typeFairness R.reduced ρred, ?_⟩
    exact ⟨ρred, hReducedFeas, rfl⟩
  have hRedNonempty' :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R'.reduced 1).Nonempty := by
    refine ⟨TypeWeightedRecommendationModel.typeFairness R'.reduced ρred', ?_⟩
    exact ⟨ρred', hReducedFeas', rfl⟩
  have hUserEq :
      RecommendationModel.optimalUserFairnessAtLevel R.data.model 1 =
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          R.reduced 1 :=
    R.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
      reps hRow 1 hOrigNonempty hRedNonempty
  have hUserEq' :
      RecommendationModel.optimalUserFairnessAtLevel R'.data.model 1 =
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          R'.reduced 1 :=
    R'.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
      reps' hRow' 1 hOrigNonempty' hRedNonempty'
  have hred_mono :
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          R.reduced 1 ≤
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          R'.reduced 1 := by
    rw [hred, hred']
    exact theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_of_alpha_le
      halpha0 halpha1 halpha0' halpha1' halpha_le
      halpha_half halpha_half' hpos hdec hsucc
  have huser_mono :
      RecommendationModel.optimalUserFairnessAtLevel R.data.model 1 ≤
        RecommendationModel.optimalUserFairnessAtLevel R'.data.model 1 := by
    rw [hUserEq, hUserEq']
    exact hred_mono
  exact R.data.model.priceOfFairness_le_of_optimalUserFairnessAtLevel_one_le
    R'.data.model hNonneg hRow hNonneg' hRow' huser_mono

/-
Theorem 3 reduced-optimum monotonicity, first-half endpoint form.  The
odd/even midpoint split is discharged internally.
-/
theorem paper_theorem3_price_decreases_firstHalf_of_reduction
    {m n : ℕ} [NeZero m] [NeZero n]
    (R R' : ReductionWitness m n 2)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (reps' : UserTypeAssignment.TypeRepresentatives R'.data.types)
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    (hred : R.reduced = twoTypeReducedModel alpha v)
    (hred' : R'.reduced = twoTypeReducedModel alpha' v)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hNonneg : R.data.model.Nonnegative)
    (hRow : R.data.model.RowHasPositiveItem)
    (hNonneg' : R'.data.model.Nonnegative)
    (hRow' : R'.data.model.RowHasPositiveItem) :
    RecommendationModel.priceOfFairness R'.data.model ≤
      RecommendationModel.priceOfFairness R.data.model := by
  rcases midpoint_center_or_succ_center (n := n) with hcenter | hsucc
  · rcases hcenter with ⟨c, hcenter⟩
    exact
      paper_theorem3_price_decreases_firstHalf_center_of_reduction
        R R' reps reps' hred hred' halpha0 halpha1 halpha0' halpha1'
        halpha_le halpha_half halpha_half' hpos hdec hcenter hNonneg hRow
        hNonneg' hRow'
  · rcases hsucc with ⟨c, hsucc⟩
    exact
      paper_theorem3_price_decreases_firstHalf_succ_center_of_reduction
        R R' reps reps' hred hred' halpha0 halpha1 halpha0' halpha1'
        halpha_le halpha_half halpha_half' hpos hdec hsucc hNonneg hRow
        hNonneg' hRow'

/-
Theorem 3 paper-facing price monotonicity, second-half form.  On the far side
of the symmetry point the constrained user optimum moves in the opposite
direction, so the price of fairness weakly increases with `α`.
-/
end OpposingTypes

namespace EstimatedRecommendationModel

/-
Exact-estimation benchmark for the price of misestimation.

If the estimated utilities coincide with the true utilities, then any policy
that solves the estimated problem has zero price of misestimation when evaluated
against the true model.
-/
end EstimatedRecommendationModel

namespace TypePolicy

/-
Appendix D, Lemma 4, Part 1: a two-type basic feasible solution has at most
`n + 1` positive `x_j,y_j` variables.
-/
end TypePolicy

/-
The Proposition 2 conclusions established for the explicit reduced equality
LP: a finite linear description of `S_symm`, existence of a symmetric optimum,
the reduced-LP BFS active-support bound, and the optimal reduced-LP BFS
shared-item bound.

The separate linear-equivalence theorem transporting basic feasible solutions
between Proposition 1's user-coordinate LP on `S_symm` and this reduced
type-coordinate LP has not yet been formalized.
-/
end GCG24UserItemFairness
