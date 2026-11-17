import Cslib.Foundations.Data.RelatesInSteps
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.List
import Mathlib.Order.WellFoundedSet
import Mathlib.Tactic.Linarith
import dep.EconCSLib.SocialChoice.FairDivision.IndivisibleGoods

namespace EconCSLib

namespace FairDivision

open scoped BigOperators

variable {Agent Item : Type*} [Finite Agent] [Finite Item] [DecidableEq Agent] [DecidableEq Item] [Nonempty Agent]

variable (v : Valuation Agent Item) {α : ℝ} (hαnonneg : 0 ≤ α) (hmargin : MarginalBound v α)

noncomputable def lmmsStep (hαnonneg : 0 ≤ α) (hmargin : MarginalBound v α) (g : Item) (state : Σ (goods : Finset Item), { A : Allocation Agent Item // IsAllocationOf A goods ∧ EnvyBoundedBy v A α }) :
    Σ (goods : Finset Item), { A : Allocation Agent Item // IsAllocationOf A goods ∧ EnvyBoundedBy v A α } :=
  let goods := state.1
  let A := state.2.val
  let halloc := state.2.property.1
  let hbound := state.2.property.2
  if hg : g ∈ goods then state else
  have hreduce := hasUnenviedReduction_of_acyclicReduction v (hasAcyclicReduction_of_envyCycleListExtraction v (hasEnvyCycleListExtraction_of_finite v))
  let reduction_exists := hreduce goods A halloc hbound
  let B := Classical.choose reduction_exists
  let owner_exists := Classical.choose_spec reduction_exists
  let owner := Classical.choose owner_exists
  let B_props := Classical.choose_spec owner_exists
  let hBalloc := B_props.1
  let hBbound := B_props.2.1
  let hunenvied := B_props.2.2
  let A_new := addItem B owner g
  let goods_new := insert g goods
  have halloc_new : IsAllocationOf A_new goods_new := sorry
  have hbound_new : EnvyBoundedBy v A_new α := sorry
  ⟨goods_new, ⟨A_new, halloc_new, hbound_new⟩⟩

noncomputable def lmmsAlgorithm (goodsList : List Item) :
    Σ (goods : Finset Item), { A : Allocation Agent Item // IsAllocationOf A goods ∧ EnvyBoundedBy v A α } :=
  goodsList.foldr (lmmsStep v hαnonneg hmargin) 
    ⟨∅, ⟨emptyAllocation Agent Item, isAllocationOf_empty, sorry⟩⟩

end FairDivision

end EconCSLib
