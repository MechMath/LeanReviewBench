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
import dep.LMMS04FairDivision.ProofInterface

open MeasureTheory

open Filter

open scoped BigOperators

open EconCSLib.FairDivision

namespace LMMS04FairDivision

namespace PaperInterface

variable {Agent Item : Type*} [Fintype Agent] [Fintype Item] [DecidableEq Agent]
  [DecidableEq Item] [Nonempty Agent] [Nonempty Item]

noncomputable section

/-- Theorem 2.1 constructive list algorithm form. -/
abbrev theorem2_1_algorithm_correct_list_toFinset.{u_3, u_4} : ∀ {Agent : Type u_3} {Item : Type u_4} [inst : Fintype.{u_3} Agent] [inst_1 : Fintype.{u_4} Item]
  [inst_2 : DecidableEq.{u_3 + 1} Agent] [inst_3 : DecidableEq.{u_4 + 1} Item] [inst_4 : Nonempty.{u_3 + 1} Agent]
  [Nonempty.{u_4 + 1} Item] (v : EconCSLib.FairDivision.Valuation.{u_3, u_4} Agent Item) {alpha : Real}
  (halpha_nonneg :
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) alpha)
  (hbound : @EconCSLib.FairDivision.MarginalBound.{u_3, u_4} Agent Item inst_3 v alpha) (goodsList : List.{u_4} Item)
  (hnodup : @List.Nodup.{u_4} Item goodsList),
  And
    (@LMMS04FairDivision.ProofInterface.isAllocationOf.{u_3, u_4} Agent Item inst_3
      (@LMMS04FairDivision.paper_lmms_algorithm.{u_3, u_4} Agent Item inst inst_1 inst_2 inst_3 inst_4 v alpha
        halpha_nonneg hbound goodsList)
      (@List.toFinset.{u_4} Item inst_3 goodsList))
    (@LMMS04FairDivision.ProofInterface.envyBoundedBy.{u_3, u_4} Agent Item v
      (@LMMS04FairDivision.paper_lmms_algorithm.{u_3, u_4} Agent Item inst inst_1 inst_2 inst_3 inst_4 v alpha
        halpha_nonneg hbound goodsList)
      alpha) := sorry

end

end PaperInterface

end LMMS04FairDivision
