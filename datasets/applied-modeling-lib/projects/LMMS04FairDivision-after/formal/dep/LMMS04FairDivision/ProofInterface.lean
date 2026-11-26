import Cslib.Foundations.Data.RelatesInSteps
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.GroupTheory.Perm.List
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.WellFoundedSet
import Mathlib.Probability.CDF
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Real.Lemmas
import dep.EconCSLib.Foundations.Optimization.Certificate
import dep.EconCSLib.SocialChoice.FairDivision.IndivisibleGoods
import dep.EconCSLib.SocialChoice.FairDivision.LMMSAlgorithm
import dep.LMMS04FairDivision.MainTheorems

open MeasureTheory

open Filter

open scoped BigOperators

open EconCSLib.FairDivision

namespace LMMS04FairDivision

namespace ProofInterface

variable {Agent Item : Type*} [Fintype Agent] [Fintype Item] [DecidableEq Agent]
  [DecidableEq Item] [Nonempty Agent] [Nonempty Item]

noncomputable section

/-- Envy of agent `i` toward agent `j`: positive part of the value difference. -/
def envy (v : Valuation Agent Item) (A : Allocation Agent Item)
    (i j : Agent) : ℝ :=
  max 0 (v.value i (A j) - v.value i (A i))

/-- Bounded-envy predicate used in Theorem 2.1. -/
def envyBoundedBy (v : Valuation Agent Item) (A : Allocation Agent Item)
    (alpha : ℝ) : Prop :=
  ∀ i j, envy v A i j ≤ alpha

/-- Allocation of exactly the specified finite set of goods. -/
def isAllocationOf (A : Allocation Agent Item) (goods : Finset Item) : Prop :=
  IsAllocationOf A goods

end

end ProofInterface

end LMMS04FairDivision
