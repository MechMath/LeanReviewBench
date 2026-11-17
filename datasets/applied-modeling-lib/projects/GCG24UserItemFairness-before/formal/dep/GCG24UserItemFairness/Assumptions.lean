import dep.GCG24UserItemFairness.MainTheorems

/-!
# Paper Assumptions: GCG24 User-Item Fairness

This file records source model assumptions and paper-statement conditions used
by the compact human-facing interface. These are not proof certificates.

The paper says that users come in `K` types. In the paper-facing Proposition 2
and Theorems 3--4 wrappers, this is encoded semantically as surjectivity of the
user-to-type map: every declared type has at least one actual user. Lean then
chooses representatives internally from that premise.
-/

namespace GCG24UserItemFairness

open scoped BigOperators

noncomputable section

/-
The source model uses strictly positive recommendation utilities. This covers
Proposition 2's symmetric model and Theorem 3's two opposing-type models.
-/
-- audit-premise: hPos : S.model.Positive
-- audit-premise: hPos' : S'.model.Positive
abbrev assumption_positive_recommendation_utilities {m n : ℕ}
    (W : RecommendationModel m n) : Prop :=
  W.Positive

/-
Proposition 2 defines types by utility rows: users with identical utility
vectors are the same type. `SymmetricData.agreeWithinTypes` records the reverse
implication, so this premise makes the partition exact rather than allowing an
arbitrary refinement of equal-utility users.
-/
-- audit-premise: hRowsDetermineTypes : S.types.UtilityRowsDetermineTypes S.model
end

end GCG24UserItemFairness
