import Cslib.Foundations.Data.RelatesInSteps
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Sort
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
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Find
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Disjoint
import Mathlib.GroupTheory.Perm.List
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.WellFoundedSet
import Mathlib.Probability.CDF
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.Order.Compact
import dep.EconCSLib.Foundations.Probability.FairCoin
import dep.EconCSLib.Foundations.Probability.FiniteExpectation
import dep.EconCSLib.MechanismDesign.Auctions.Combinatorial
import dep.EconCSLib.MechanismDesign.Auctions.DigitalGoods
import dep.EconCSLib.MechanismDesign.Auctions.Position
import dep.EconCSLib.SocialChoice.FairDivision.IndivisibleGoods
import dep.GHW01DigitalGoods.Assumptions
import dep.GHW01DigitalGoods.AuctionMainTheorems
import dep.GHW01DigitalGoods.BoundedSourceDefinitions
import dep.GHW01DigitalGoods.BoundedSupply
import dep.GHW01DigitalGoods.MainTheorems
import dep.GHW01DigitalGoods.SourceDefinitions

namespace GHW01DigitalGoods

namespace PaperInterface

open EconCSLib.Auction

open scoped BigOperators

noncomputable section

/--
Digital-goods auction revenue: the sum of sale prices of selected bids.

The source outcome model represents an outcome as a set, so a selected bid is
encoded by allocation `1`. This definition deliberately excludes a payment
attached to every other library allocation value; the paper-facing theorem
below makes the required binary-outcome convention explicit.
-/
def revenue {Agent : Type*} [Fintype Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) : ℝ :=
  ∑ i : Agent, if M.allocation values i = 1 then M.payment values i else 0

/--
Dominant-strategy truthfulness: truthful bidding weakly dominates replacing
one agent's value report by any alternative report.

Source status: direct source definition; the reviewed theorem immediately
below proves the definition unfolds to the exact dominant-strategy formula.
-/
def truthful {Agent : Type*} [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent) : Prop :=
  ∀ (values : Agent → ℝ) (i : Agent) (report : ℝ),
    M.utility values i (Function.update values i report) ≤
      M.utility values i values

/--
Total bid value `T = sum_i v_i`.

Source status: direct source text.
Source note: GHW define `T` as the sum of all bids in the input profile.
-/
def totalValue {Agent : Type*} [Fintype Agent] (values : Agent → ℝ) : ℝ :=
  ∑ i : Agent, values i

/--
Theorem 9.3: deterministic truthful auctions have an attained lower-bound
witness for every positive source constant `alpha`.

The input is the paper's deterministic set-of-bids source model.  Its focused
outcome field is the Section 9.3 slice `g(x) = A_i(B_i^x)`.  The model carries
the set-of-bids-to-erased-multiset representation as an explicit source-model
premise; the theorem derives the internal erased-list relabeling needed by the
two-value lower-bound construction.

Source status: source theorem under documented source-model conventions.
Source note: the checked target makes the source's sale-price convention,
set-of-bids-to-erased-multiset representation bridge, and integer high-value
domain explicit.  It proves the displayed `1 / H` witness on that target; it
also records that `H` occurs in the binary input, and does not claim the
unrestricted archival quantification verbatim.
-/
def theorem9_3_deterministic_truthful_lower_boundSpec : Prop :=
  ∀ {highValue : ℕ} {alpha : ℝ}
    (model : assumption_theorem9_3_primitive_set_of_bids_deterministic_source_model highValue)
    (_hhigh_ge_two : 2 ≤ highValue) (_halpha_pos : 0 < alpha),
    ∃ highCount lowCount : ℕ,
      0 < highCount ∧
      revenue (model.auctionFamily highCount lowCount)
          (twoValueBidProfile highValue highCount lowCount) /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * alpha ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount

theorem theorem9_3_deterministic_truthful_lower_bound :
    theorem9_3_deterministic_truthful_lower_boundSpec := sorry

end

end PaperInterface

end GHW01DigitalGoods
