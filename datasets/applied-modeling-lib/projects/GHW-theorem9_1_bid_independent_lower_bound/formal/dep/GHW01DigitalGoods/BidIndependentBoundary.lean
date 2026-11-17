import Cslib.Foundations.Data.RelatesInSteps
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Count
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Find
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.GroupTheory.Perm.List
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.WellFoundedSet
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.Order.Compact
import dep.EconCSLib.Foundations.Probability.FairCoin
import dep.EconCSLib.Foundations.Probability.FiniteExpectation
import dep.EconCSLib.MechanismDesign.Auctions.Combinatorial
import dep.EconCSLib.MechanismDesign.Auctions.DigitalGoods
import dep.EconCSLib.MechanismDesign.Auctions.Position
import dep.EconCSLib.SocialChoice.FairDivision.IndivisibleGoods
import dep.GHW01DigitalGoods.AuctionMainTheorems

namespace GHW01DigitalGoods

open EconCSLib.Auction

structure PaperBidIndependentBoundaryRule where
  price : Multiset ℝ → ℝ
  acceptsEquality : Multiset ℝ → Bool

/-- Payment obtained from one bidder under the source's strict-or-weak
threshold convention. -/
noncomputable def paperBidIndependentBoundaryPayment
    (rule : PaperBidIndependentBoundaryRule) (others : Multiset ℝ) (bid : ℝ) : ℝ :=
  if rule.acceptsEquality others then
    if rule.price others ≤ bid then rule.price others else 0
  else if rule.price others < bid then rule.price others else 0

/--
Revenue of a Section 5.1 source bid-independent rule on the binary input used
in Theorem 9.1.  Each bidder's price and equality convention are computed from
that bidder's erased bid multiset, so the `>=`/`>` choice can vary with the
other bids while remaining invariant to their presentation order.
-/
noncomputable def twoValueBidIndependentBoundaryRevenue
    (rule : PaperBidIndependentBoundaryRule)
    (highValue highCount lowCount : ℕ) : ℝ :=
  (highCount : ℝ) *
      paperBidIndependentBoundaryPayment rule
        (Multiset.ofList
          (twoValueErasedBidList highValue (highCount - 1) lowCount))
        (highValue : ℝ) +
    (lowCount : ℝ) *
      paperBidIndependentBoundaryPayment rule
        (Multiset.ofList
          (twoValueErasedBidList highValue highCount (lowCount - 1))) 1

end GHW01DigitalGoods
