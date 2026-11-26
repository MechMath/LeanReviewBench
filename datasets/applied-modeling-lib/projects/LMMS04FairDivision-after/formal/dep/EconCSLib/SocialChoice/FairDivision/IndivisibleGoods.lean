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

/-- The allocation assigning every agent the empty bundle. -/
def emptyAllocation (Agent Item : Type*) : Allocation Agent Item :=
  fun _ => ∅

/--
A valuation profile for indivisible goods.

The first fair-division target only needs monotone set valuations; additivity
and normalization should be separate assumptions for later papers.
-/
structure Valuation (Agent Item : Type*) where
  value : Agent → Bundle Item → ℝ
  monotone : ∀ agent {S T : Bundle Item}, S ⊆ T → value agent S ≤ value agent T

variable {Agent Item : Type*}

/-- Envy of `i` for `j` under allocation `A`. -/
def envy (v : Valuation Agent Item) (A : Allocation Agent Item) (i j : Agent) : ℝ :=
  max 0 (v.value i (A j) - v.value i (A i))

/-- Every pairwise envy is bounded by `α`. -/
def EnvyBoundedBy (v : Valuation Agent Item) (A : Allocation Agent Item) (α : ℝ) : Prop :=
  ∀ i j, envy v A i j ≤ α

/-- `A` allocates exactly the goods in `goods`, with no duplicates and no outsiders. -/
def IsAllocationOf [DecidableEq Item] (A : Allocation Agent Item) (goods : Finset Item) : Prop :=
  (∀ i g, g ∈ A i → g ∈ goods) ∧
    ∀ g, g ∈ goods → ∃! i, g ∈ A i

theorem isAllocationOf_empty [DecidableEq Item] :
    IsAllocationOf (emptyAllocation Agent Item) (∅ : Finset Item) := sorry

/-- The paper's maximum-marginal-utility hypothesis, expressed as an upper bound. -/
def MarginalBound [DecidableEq Item] (v : Valuation Agent Item) (α : ℝ) : Prop :=
  ∀ agent (S : Bundle Item) (g : Item),
    v.value agent (insert g S) - v.value agent S ≤ α

/-- Nobody envies the bundle currently held by `owner`. -/
def NoOneEnvies (v : Valuation Agent Item) (A : Allocation Agent Item)
    (owner : Agent) : Prop :=
  ∀ i, v.value i (A owner) ≤ v.value i (A i)

/-- Directed envy edge: `i` strictly prefers `j`'s bundle to her own. -/
def EnvyEdge (v : Valuation Agent Item) (A : Allocation Agent Item)
    (i j : Agent) : Prop :=
  v.value i (A i) < v.value i (A j)

/--
The directed envy graph is acyclic when the incoming-edge relation is
well-founded. This is the exact graph-theoretic condition needed to produce a
source/unenvied agent.
-/
def AcyclicEnvyGraph (v : Valuation Agent Item) (A : Allocation Agent Item) :
    Prop :=
  WellFounded fun i j => EnvyEdge v A i j

/-- Give one additional good to `owner`. -/
def addItem [DecidableEq Agent] [DecidableEq Item]
    (A : Allocation Agent Item) (owner : Agent) (g : Item) :
    Allocation Agent Item :=
  fun i => if i = owner then insert g (A i) else A i

theorem isAllocationOf_addItem_insert [DecidableEq Agent] [DecidableEq Item]
    (A : Allocation Agent Item) (goods : Finset Item) (owner : Agent) (g : Item)
    (halloc : IsAllocationOf A goods)
    (hg : g ∉ goods) :
    IsAllocationOf (addItem A owner g) (insert g goods) := sorry

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

/--
List-facing version of the remaining simple-cycle extraction seam.  This is
often easier to prove from a concrete directed cycle than constructing the
permutation directly.
-/
def HasEnvyCycleListExtraction [DecidableEq Agent]
    (v : Valuation Agent Item) : Prop :=
  ∀ A : Allocation Agent Item,
    ¬ AcyclicEnvyGraph v A → Nonempty (EnvyCycleList v A)

/--
Finite non-acyclic envy graphs contain an explicit simple envy cycle.  This
closes the graph-theoretic cycle-extraction step used by the LMMS proof.
-/
theorem hasEnvyCycleListExtraction_of_finite
    [Finite Agent] [DecidableEq Agent] (v : Valuation Agent Item) :
    HasEnvyCycleListExtraction v := sorry

theorem envyBoundedBy_addItem_of_unenvied [DecidableEq Agent] [DecidableEq Item]
    (v : Valuation Agent Item) (A : Allocation Agent Item)
    (owner : Agent) (g : Item) {α : ℝ}
    (hαnonneg : 0 ≤ α)
    (hbound : EnvyBoundedBy v A α)
    (hmargin : MarginalBound v α)
    (hunenvied : NoOneEnvies v A owner) :
    EnvyBoundedBy v (addItem A owner g) α := sorry

/--
The paper's cycle-elimination step, packaged as the exact property needed by
the main induction: every bounded partial allocation can be transformed into a
bounded allocation of the same goods with an unenvied owner.
-/
def HasUnenviedReduction [DecidableEq Item]
    (v : Valuation Agent Item) (α : ℝ) : Prop :=
  ∀ goods (A : Allocation Agent Item),
    IsAllocationOf A goods →
    EnvyBoundedBy v A α →
    ∃ B owner, IsAllocationOf B goods ∧ EnvyBoundedBy v B α ∧ NoOneEnvies v B owner

/--
Cycle elimination target used by the paper proof: every bounded partial
allocation can be transformed into one with an acyclic envy graph while
preserving the allocated goods and the envy bound.
-/
def HasAcyclicReduction [DecidableEq Item]
    (v : Valuation Agent Item) (α : ℝ) : Prop :=
  ∀ goods (A : Allocation Agent Item),
    IsAllocationOf A goods →
    EnvyBoundedBy v A α →
    ∃ B, IsAllocationOf B goods ∧ EnvyBoundedBy v B α ∧ AcyclicEnvyGraph v B

/--
Finite cycle elimination stated with a simple-cycle list extractor.
-/
theorem hasAcyclicReduction_of_envyCycleListExtraction
    [Finite Agent] [Finite Item] [DecidableEq Agent] [DecidableEq Item]
    (v : Valuation Agent Item) {α : ℝ}
    (hextract : HasEnvyCycleListExtraction v) :
    HasAcyclicReduction v α := sorry

theorem hasUnenviedReduction_of_acyclicReduction
    [DecidableEq Item] [Nonempty Agent]
    (v : Valuation Agent Item) {α : ℝ}
    (hreduce : HasAcyclicReduction v α) :
    HasUnenviedReduction v α := sorry

end FairDivision

end EconCSLib
