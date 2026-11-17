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

open scoped BigOperators

namespace EconCSLib

namespace FairDivision

/-- A bundle of indivisible goods. -/
abbrev Bundle (Item : Type*) := Finset Item

/-- An allocation assigns each agent a bundle. -/
abbrev Allocation (Agent Item : Type*) := Agent → Bundle Item

/--
A valuation profile for indivisible goods.

The first fair-division target only needs monotone set valuations; additivity
and normalization should be separate assumptions for later papers.
-/
structure Valuation (Agent Item : Type*) where
  value : Agent → Bundle Item → ℝ
  monotone : ∀ agent {S T : Bundle Item}, S ⊆ T → value agent S ≤ value agent T

variable {Agent Item : Type*}

/-- Directed envy edge: `i` strictly prefers `j`'s bundle to her own. -/
def EnvyEdge (v : Valuation Agent Item) (A : Allocation Agent Item)
    (i j : Agent) : Prop :=
  v.value i (A i) < v.value i (A j)

/--
A simple envy cycle as a nodup list.  `cycle.formPerm` maps every listed agent to
the next listed agent, wrapping the last agent to the first.
-/
structure EnvyCycleList [DecidableEq Agent]
    (v : Valuation Agent Item) (A : Allocation Agent Item) where
  cycle : List Agent
  nodup : cycle.Nodup
  length_two : 2 ≤ cycle.length
  edge_formPerm : ∀ i, i ∈ cycle → EnvyEdge v A i (cycle.formPerm i)

namespace EnvyCycleList

end EnvyCycleList

/--
An envy-cycle permutation: outside the cycle `next` may fix agents, while on
the cycle each moved agent points to a bundle she strictly envies.
-/
structure EnvyCyclePermutation
    (v : Valuation Agent Item) (A : Allocation Agent Item) where
  next : Agent → Agent
  bijective : Function.Bijective next
  fixed_or_envy : ∀ i, next i = i ∨ EnvyEdge v A i (next i)
  some_envy : ∃ i, EnvyEdge v A i (next i)

namespace EnvyCyclePermutation

end EnvyCyclePermutation

/--
Certificate for the local rotation produced by an envy cycle: the successor map
is a permutation, every agent weakly improves her own bundle, and at least one
agent strictly improves.
-/
structure ImprovingBundleRotation
    (v : Valuation Agent Item) (A : Allocation Agent Item) where
  next : Agent → Agent
  bijective : Function.Bijective next
  self_improves : ∀ i, v.value i (A i) ≤ v.value i (A (next i))
  some_strict : ∃ i, v.value i (A i) < v.value i (A (next i))

namespace ImprovingBundleRotation

end ImprovingBundleRotation

end FairDivision

end EconCSLib
