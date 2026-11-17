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
import dep.EconCSLib.SocialChoice.FairDivision.IndivisibleGoods
import dep.EconCSLib.SocialChoice.FairDivision.LMMSAlgorithm

open MeasureTheory

open Filter

open EconCSLib.FairDivision

namespace LMMS04FairDivision

variable {Agent Item : Type*} [Fintype Agent] [Fintype Item] [DecidableEq Agent] [DecidableEq Item] [Nonempty Agent] [Nonempty Item]

/-- Theorem 2.1 (Algorithm): The LMMS algorithm produces a bounded-envy allocation. -/
noncomputable def paper_lmms_algorithm
    (v : Valuation Agent Item) {α : ℝ} (hαnonneg : 0 ≤ α) (hbound : MarginalBound v α) (goodsList : List Item) :
    Allocation Agent Item :=
  (lmmsAlgorithm v hαnonneg hbound goodsList).2.val

end LMMS04FairDivision
