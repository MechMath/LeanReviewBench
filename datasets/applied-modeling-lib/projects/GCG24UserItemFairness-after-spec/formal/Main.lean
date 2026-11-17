import Mathlib

import dep.GCG24UserItemFairness.ProofBridge

namespace GCG24UserItemFairness

namespace PaperInterface

open scoped BigOperators
open GCG24UserItemFairness.ProofBridge
noncomputable section

/- Source-facing semantic target for the definition `recommendationUtility`. -/
def theorem3_price_decreases_first_halfSpec
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
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) : Prop :=
  RecommendationModel.priceOfFairness S'.model ≤
    RecommendationModel.priceOfFairness S.model

/- Source-facing semantic target for `theorem3_price_increases_second_half`. -/
end

end PaperInterface
end GCG24UserItemFairness
