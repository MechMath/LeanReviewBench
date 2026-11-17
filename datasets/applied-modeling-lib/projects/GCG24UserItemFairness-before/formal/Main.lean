import Mathlib

import dep.GCG24UserItemFairness.MainTheorems
import dep.GCG24UserItemFairness.Assumptions
namespace GCG24UserItemFairness
namespace PaperInterface

open scoped BigOperators

noncomputable section

/-! ## Paper Definitions -/

/- Recommendation utility matrix `w_{ij}` for users and items. -/
theorem theorem3_price_decreases_first_half
    {m n : ℕ} [NeZero m] [NeZero n]
    (S S' : RecommendationModel.SymmetricData m n 2)
    (hTypes : Function.Surjective S.types.toType)
    (hTypes' : Function.Surjective S'.types.toType)
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    (hred : (S.canonicalReductionOfSurjective hTypes).reduced =
      OpposingTypes.twoTypeReducedModel alpha v)
    (hred' : (S'.canonicalReductionOfSurjective hTypes').reduced =
      OpposingTypes.twoTypeReducedModel alpha' v)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) :
    RecommendationModel.priceOfFairness S'.model ≤
      RecommendationModel.priceOfFairness S.model := by
  let reps : UserTypeAssignment.TypeRepresentatives S.types :=
    EconCSLib.Policy.FiberRepresentatives.ofSurjective hTypes
  let reps' : UserTypeAssignment.TypeRepresentatives S'.types :=
    EconCSLib.Policy.FiberRepresentatives.ofSurjective hTypes'
  have hPos : assumption_positive_recommendation_utilities S.model := by
    intro u j
    change 0 < (S.canonicalReductionOfSurjective hTypes).data.model.utility u j
    rw [(S.canonicalReductionOfSurjective hTypes).utility_agrees u j, hred]
    exact OpposingTypes.twoTypeReducedModel_positiveUtilities alpha v hpos _ _
  have hPos' : assumption_positive_recommendation_utilities S'.model := by
    intro u j
    change 0 < (S'.canonicalReductionOfSurjective hTypes').data.model.utility u j
    rw [(S'.canonicalReductionOfSurjective hTypes').utility_agrees u j, hred']
    exact OpposingTypes.twoTypeReducedModel_positiveUtilities alpha' v hpos _ _
  have hNonneg : S.model.Nonnegative :=
    RecommendationModel.nonnegative_of_positive S.model hPos
  have hRow : S.model.RowHasPositiveItem :=
    RecommendationModel.rowHasPositiveItem_of_positive S.model hPos
  have hNonneg' : S'.model.Nonnegative :=
    RecommendationModel.nonnegative_of_positive S'.model hPos'
  have hRow' : S'.model.RowHasPositiveItem :=
    RecommendationModel.rowHasPositiveItem_of_positive S'.model hPos'
  exact OpposingTypes.paper_theorem3_price_decreases_firstHalf_of_reduction
    (S.canonicalReduction reps) (S'.canonicalReduction reps')
    reps reps' hred hred' halpha0 halpha1 halpha0' halpha1'
    halpha_le halpha_half halpha_half' hpos hdec hNonneg hRow hNonneg' hRow'

/-
Theorem 3, second half: in the opposing two-type model, increasing `alpha`
away from `1 / 2` weakly increases the price of fairness.
-/
end

end PaperInterface
end GCG24UserItemFairness
