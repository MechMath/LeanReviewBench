import Mathlib
import dep.GCG24UserItemFairness.OpposingTypes

namespace GCG24UserItemFairness
namespace ProofBridge

open scoped BigOperators

noncomputable section

/-! ## Paper Definitions -/

/- Recommendation utility matrix `w_{ij}` for users and items. -/
def rawUserUtility {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n) (u : User m) : ℝ :=
  EconCSLib.Policy.agentScore ρ W.utility u

/- Normalized user utility `U_i(rho)`. -/
def normalizedUserUtility {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) (u : User m) : ℝ :=
  rawUserUtility W ρ u / RecommendationModel.bestItemUtility W u

/-
Source status: direct source text
User fairness objective for a recommendation policy.
-/
def userFairness {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) : ℝ :=
  EconCSLib.finiteMin (normalizedUserUtility W ρ)

/- The direct paper-facing user objective is definitionally the library
objective; no policy or utility condition is introduced by this interface. -/
def rawItemUtility {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n) (j : Item n) : ℝ :=
  ∑ u, W.utility u j * (ρ u j).toReal

/- Item normalizer `sum_i w_ij`. -/
def itemNormalizer {m n : ℕ}
    (W : RecommendationModel m n) (j : Item n) : ℝ :=
  ∑ u, W.utility u j

/- Normalized item utility `I_j(rho)`. -/
def normalizedItemUtility {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n) (j : Item n) : ℝ :=
  rawItemUtility W ρ j / itemNormalizer W j

/-
Source status: direct source text
Item fairness objective for a recommendation policy.
-/
def itemFairness {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) : ℝ :=
  EconCSLib.finiteMin (normalizedItemUtility W ρ)

/-
The paper-facing quotient agrees with the library definition on every Lean
model: Lean division already evaluates a zero denominator as zero, matching
the library's explicit totalization.  The source's strict positivity still
ensures this defensive branch is outside its intended ratio domain.
-/
def priceOfFairnessAt {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) : ℝ :=
  (RecommendationModel.optimalUserFairnessAtLevel W 0 -
      RecommendationModel.optimalUserFairnessAtLevel W γ) /
    RecommendationModel.optimalUserFairnessAtLevel W 0

/-
The paper-facing quotient agrees with the library's explicit zero-baseline
totalization on every Lean model, because Lean division by zero is itself
zero.  The source's strict positivity remains the intended ordinary-ratio
domain.
-/
def priceOfFairness {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) : ℝ :=
  priceOfFairnessAt W 1

/- The direct maximal-item-fairness price agrees with the library definition. -/
end

end ProofBridge
end GCG24UserItemFairness
