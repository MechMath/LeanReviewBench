import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Probability.CDF
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.ProjIcc
import dep.AppliedModelingLib.Applications.RecommenderSystems.Allocation
import dep.AppliedModelingLib.Foundations.Math.Asymptotics
import dep.AppliedModelingLib.Foundations.Probability.OrderStatistics
import dep.AppliedModelingLib.Foundations.Probability.PMFKernel
import dep.PRPKG24AccuracyDiversity.Basic
import dep.PRPKG24AccuracyDiversity.Exchange
import dep.PRPKG24AccuracyDiversity.Representation
import dep.PRPKG24AccuracyDiversity.TopKOracle

open Filter Topology

open scoped BigOperators

namespace PRPKG24AccuracyDiversity

/--
The paper's `γ = ∞` profile: all representation mass is assigned to a chosen
type whose likelihood is maximal.
-/
structure InfiniteGammaHomogeneityProfile (T : ℕ) where
  likelihood : ItemType T → ℝ
  best : ItemType T
  isArgmax : ∀ t : ItemType T, likelihood t ≤ likelihood best

namespace InfiniteGammaHomogeneityProfile

/-- Target share for the `γ = ∞` profile. -/
noncomputable def targetShare {T : ℕ}
    (G : InfiniteGammaHomogeneityProfile T) (t : ItemType T) : ℝ :=
  if t = G.best then 1 else 0

end InfiniteGammaHomogeneityProfile

namespace GammaHomogeneityProfile

end GammaHomogeneityProfile

/--
A sequence of feasible finite allocations, matching the paper's `{S_n}` after
passing from sets to type-count vectors.
-/
structure AllocationSequence (T : ℕ) where
  allocation : ℕ → CountAllocation T
  feasible : ∀ N, ConsumptionModel.FeasibleAtTotal N (allocation N)

namespace AllocationSequence

end AllocationSequence

/-- A sequence selecting an optimum of the `N`th finite problem for each `N`. -/
structure OptimalAllocationSequence {T : ℕ}
    (Mseq : ℕ → ConsumptionModel T) where
  allocation : ℕ → CountAllocation T
  optimal : ∀ N, (Mseq N).IsOptimalAtTotal N (allocation N)

namespace OptimalAllocationSequence

end OptimalAllocationSequence

/--
Bridge PRPKG's paper-local top-`k` oracle to the reusable probability
order-statistic interface in `AppliedModelingLib`.
-/
def topKExpectationOracleOfTopKValueOracle {T : ℕ}
    (O : TopKValueOracle T) :
    AppliedModelingLib.Probability.TopKExpectationOracle (ItemType T) where
  expectedTopSum := O.expectedTopSum

/--
Reusable probability-facing certificate for Theorem 1(ii)-(iv): the top-`k`
marginal has a common asymptotic scale and type weight.
-/
abbrev TopKScaledMarginalLimitCertificate {T : ℕ}
    (O : TopKValueOracle T) (k : ℕ)
    (scale : ℕ → ℝ) (weight : ItemType T → ℝ) :=
  AppliedModelingLib.Probability.TopKExpectationOracle.ScaledMarginalLimitCertificate
    (topKExpectationOracleOfTopKValueOracle O) k scale weight

namespace TopKScaledMarginalLimitCertificate

end TopKScaledMarginalLimitCertificate

/--
Reusable finite-to-asymptotic bridge for Lemma D.1-style conclusions.

If all finite optima have pairwise bounded scaled counts
`count t / weight t`, then their counts are uniformly `O(1)` close to the
allocation with shares proportional to `weight`, hence the induced
representations converge at exact `C / N` rate.
-/
structure PairwiseScaledHomogeneityCertificate {T : ℕ} [NeZero T]
    (Mseq : ℕ → ConsumptionModel T) (weight : ItemType T → ℝ)
    (G : GammaHomogeneityProfile T) where
  weight_pos : ∀ t, 0 < weight t
  targetShare_eq :
    ∀ t, G.targetShare t = weight t / ∑ i : ItemType T, weight i
  scaled_bound : ℝ
  scaled_bound_pos : 0 < scaled_bound
  pairwise_scaled :
    ∀ N (a : CountAllocation T), 0 < N → (Mseq N).IsOptimalAtTotal N a →
      ∀ i j,
        |(a.count i : ℝ) / weight i -
          (a.count j : ℝ) / weight j| ≤ scaled_bound

namespace PairwiseScaledHomogeneityCertificate

end PairwiseScaledHomogeneityCertificate

/--
Sublinear pairwise-scaled bridge for Lemma D.1-style asymptotic proofs.

This weakens `PairwiseScaledHomogeneityCertificate`: the scaled counts may
differ by `ε_N * N`, provided `ε_N → 0`. After averaging, representation error
is at most `ε_N` times the total target weight.
-/
structure PairwiseScaledSublinearHomogeneityCertificate {T : ℕ} [NeZero T]
    (Mseq : ℕ → ConsumptionModel T) (weight : ItemType T → ℝ)
    (G : GammaHomogeneityProfile T) where
  weight_pos : ∀ t, 0 < weight t
  targetShare_eq :
    ∀ t, G.targetShare t = weight t / ∑ i : ItemType T, weight i
  error : ℕ → ℝ
  error_nonneg : ∀ N, 0 ≤ error N
  error_tends_to_zero : AppliedModelingLib.Math.TendsToZero error
  pairwise_scaled :
    ∀ N (a : CountAllocation T), 0 < N → (Mseq N).IsOptimalAtTotal N a →
      ∀ i j,
        |(a.count i : ℝ) / weight i -
          (a.count j : ℝ) / weight j| ≤ error N * (N : ℝ)

namespace PairwiseScaledSublinearHomogeneityCertificate

end PairwiseScaledSublinearHomogeneityCertificate

/--
FOC-based sublinear pairwise-scaled bridge.

This is the reusable endpoint for asymptotic product estimates: if every
scaled-count gap larger than `error N * N` would make the source backward
marginal strictly smaller than the destination forward marginal, then the
finite first-order condition rules out such gaps in every optimum. The existing
sublinear pairwise-scaled bridge then gives asymptotic homogeneity.
-/
structure PairwiseScaledSublinearFOCCertificate {T : ℕ} [NeZero T]
    (Mseq : ℕ → ConsumptionModel T) (weight : ItemType T → ℝ)
    (G : GammaHomogeneityProfile T) where
  weight_pos : ∀ t, 0 < weight t
  targetShare_eq :
    ∀ t, G.targetShare t = weight t / ∑ i : ItemType T, weight i
  error : ℕ → ℝ
  error_nonneg : ∀ N, 0 ≤ error N
  error_tends_to_zero : AppliedModelingLib.Math.TendsToZero error
  large_gap_backward_lt_forward :
    ∀ N (a : CountAllocation T), 0 < N → (Mseq N).IsOptimalAtTotal N a →
      ∀ src dst,
        error N * (N : ℝ) <
          (a.count src : ℝ) / weight src -
            (a.count dst : ℝ) / weight dst →
        (Mseq N).weightedBackwardMarginal src (a.count src) <
          (Mseq N).weightedForwardMarginal dst (a.count dst)

namespace PairwiseScaledSublinearFOCCertificate

end PairwiseScaledSublinearFOCCertificate

/--
Floor-aware version of the pairwise-scaled FOC bridge.

Distribution-specific estimates often prove the large-gap marginal dominance
only after every compared count is above a fixed floor and after the total
problem size is large.  This certificate records those eventual facts and
absorbs the finite prefix by using a deliberately large temporary error, then
produces the clean `PairwiseScaledSublinearFOCCertificate`.
-/
structure PairwiseScaledEventualSublinearFOCCertificate {T : ℕ} [NeZero T]
    (Mseq : ℕ → ConsumptionModel T) (weight : ItemType T → ℝ)
    (G : GammaHomogeneityProfile T) where
  weight_pos : ∀ t, 0 < weight t
  targetShare_eq :
    ∀ t, G.targetShare t = weight t / ∑ i : ItemType T, weight i
  base_error : ℕ → ℝ
  base_error_nonneg : ∀ N, 0 ≤ base_error N
  base_error_tends_to_zero : AppliedModelingLib.Math.TendsToZero base_error
  floor : ℕ
  count_floor_eventually :
    ∀ᶠ N in atTop,
      ∀ a : CountAllocation T, 0 < N → (Mseq N).IsOptimalAtTotal N a →
        ∀ t, floor < a.count t
  large_gap_backward_lt_forward_after_floor :
    ∀ᶠ N in atTop,
      ∀ a : CountAllocation T, 0 < N → (Mseq N).IsOptimalAtTotal N a →
        ∀ src dst,
          floor < a.count src →
          floor < a.count dst →
          base_error N * (N : ℝ) <
            (a.count src : ℝ) / weight src -
              (a.count dst : ℝ) / weight dst →
          (Mseq N).weightedBackwardMarginal src (a.count src) <
            (Mseq N).weightedForwardMarginal dst (a.count dst)

namespace PairwiseScaledEventualSublinearFOCCertificate

end PairwiseScaledEventualSublinearFOCCertificate

/--
Top-`k` source-shaped sublinear FOC certificate for Theorem 1(i).

For the finite-discrete branch, the remaining probability/order-statistic work
should prove the `large_gap_backward_lt_forward` field: if one type has more
than `error N * N` extra recommendations relative to another, then the source's
last-item top-`k` marginal is strictly smaller than the destination's next-item
top-`k` marginal. This specialized certificate avoids exposing reviewers to
the generic scaled-weight interface when the target is uniform.
-/
structure TopKUniformSublinearFOCCertificate {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) where
  error : ℕ → ℝ
  error_nonneg : ∀ N, 0 ≤ error N
  error_tends_to_zero : AppliedModelingLib.Math.TendsToZero error
  large_gap_backward_lt_forward :
    ∀ N (a : CountAllocation T), 0 < N →
      (O.toConsumptionModel likelihood k).IsOptimalAtTotal N a →
      ∀ src dst,
        error N * (N : ℝ) < (a.count src : ℝ) - (a.count dst : ℝ) →
        likelihood src *
            (O.expectedTopSum k src (a.count src) -
              O.expectedTopSum k src (a.count src - 1)) <
          likelihood dst *
            (O.expectedTopSum k dst (a.count dst + 1) -
              O.expectedTopSum k dst (a.count dst))

namespace TopKUniformSublinearFOCCertificate

end TopKUniformSublinearFOCCertificate

/--
Count-floor certificate for source Theorem 1(i)'s top-`k` route.

If every sufficiently large source count has a last-item marginal below every
destination count at or below `floor`, then no large finite optimum can leave a
type at or below that floor: moving one recommendation from an overlarge source
to the underfilled destination would strictly improve the objective.
-/
structure TopKUniformCountFloorCertificate {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) where
  floor : ℕ
  source_threshold : ℕ
  floor_le_source_threshold : floor ≤ source_threshold
  backward_lt_forward_to_floor :
    ∀ src dst qsrc qdst,
      source_threshold < qsrc →
      qdst ≤ floor →
      likelihood src *
          (O.expectedTopSum k src qsrc -
            O.expectedTopSum k src (qsrc - 1)) <
        likelihood dst *
          (O.expectedTopSum k dst (qdst + 1) -
            O.expectedTopSum k dst qdst)

namespace TopKUniformCountFloorCertificate

theorem count_floor_eventually {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert : TopKUniformCountFloorCertificate O likelihood k) :
    ∀ᶠ N in atTop,
      ∀ a : CountAllocation T, 0 < N →
        (O.toConsumptionModel likelihood k).IsOptimalAtTotal N a →
        ∀ t, hcert.floor < a.count t := sorry

end TopKUniformCountFloorCertificate

/--
Eventual, floor-dependent top-`k` FOC certificate for Theorem 1(i).

Distribution-level order-statistic estimates are typically only available once
both compared type counts are above a fixed floor and the total slate size is
large.  This certificate records that source-shaped obligation, together with
the matching eventual count-floor fact for finite optima.  The wrapper below
absorbs the finite prefix by assigning a deliberately large temporary error,
then produces the clean `TopKUniformSublinearFOCCertificate` consumed by the
paper-facing theorem.
-/
structure TopKUniformEventualSublinearFOCCertificate {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) where
  base_error : ℕ → ℝ
  base_error_nonneg : ∀ N, 0 ≤ base_error N
  base_error_tends_to_zero : AppliedModelingLib.Math.TendsToZero base_error
  floor : ℕ
  count_floor_eventually :
    ∀ᶠ N in atTop,
      ∀ a : CountAllocation T, 0 < N →
        (O.toConsumptionModel likelihood k).IsOptimalAtTotal N a →
        ∀ t, floor < a.count t
  large_gap_backward_lt_forward_after_floor :
    ∀ᶠ N in atTop,
      ∀ src dst qsrc qdst,
        qsrc ≤ N →
        qdst ≤ N →
        floor < qsrc →
        floor < qdst →
        base_error N * (N : ℝ) < (qsrc : ℝ) - (qdst : ℝ) →
        likelihood src *
            (O.expectedTopSum k src qsrc -
              O.expectedTopSum k src (qsrc - 1)) <
          likelihood dst *
            (O.expectedTopSum k dst (qdst + 1) -
              O.expectedTopSum k dst qdst)

namespace TopKUniformEventualSublinearFOCCertificate

end TopKUniformEventualSublinearFOCCertificate

/--
Finite-discrete geometric marginal-bound certificate for Theorem 1(i).

The source proof bounds top-`k` marginals by a polynomial-times-geometric upper
tail and a geometric lower tail.  This certificate is the optimization-facing
form of that probability estimate: it supplies the marginal bounds and a
sublinear integer gap schedule whose polynomial-geometric product is eventually
smaller than the lower-tail constant.
-/
structure TopKUniformGeometricMarginalBoundCertificate {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) where
  rho : ℝ
  rho_pos : 0 < rho
  rho_lt_one : rho < 1
  floor : ℕ
  source_threshold : ℕ
  floor_le_source_threshold : floor ≤ source_threshold
  floor_backward_lt_forward :
    ∀ src dst qsrc qdst,
      source_threshold < qsrc →
      qdst ≤ floor →
      likelihood src *
          (O.expectedTopSum k src qsrc -
            O.expectedTopSum k src (qsrc - 1)) <
        likelihood dst *
          (O.expectedTopSum k dst (qdst + 1) -
            O.expectedTopSum k dst qdst)
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  degree : ℕ
  gap : ℕ → ℕ
  gap_error_tends_to_zero :
    AppliedModelingLib.Math.TendsToZero
      (fun N => ((gap N + 1 : ℕ) : ℝ) / (N : ℝ))
  gap_dominance_eventually :
    ∀ᶠ (N : ℕ) in atTop,
      upper * (N : ℝ) ^ degree * rho ^ (gap N) < lower
  weighted_backward_upper :
    ∀ src qsrc,
      floor < qsrc →
      likelihood src *
          (O.expectedTopSum k src qsrc -
            O.expectedTopSum k src (qsrc - 1)) ≤
        upper * (qsrc : ℝ) ^ degree * rho ^ qsrc
  weighted_forward_lower :
    ∀ dst qdst,
      floor < qdst →
      lower * rho ^ qdst ≤
        likelihood dst *
          (O.expectedTopSum k dst (qdst + 1) -
            O.expectedTopSum k dst qdst)

namespace TopKUniformGeometricMarginalBoundCertificate

end TopKUniformGeometricMarginalBoundCertificate

/--
Finite-discrete geometric tail certificate for Theorem 1(i).

This is one step closer to the source distribution argument than
`TopKUniformGeometricMarginalBoundCertificate`: it assumes a positive lower
bound on the finitely many destination marginals up to the floor, and derives
the large-source/small-destination count-floor comparison from the geometric
upper tail.
-/
structure TopKUniformGeometricTailCertificate {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) where
  rho : ℝ
  rho_pos : 0 < rho
  rho_lt_one : rho < 1
  floor : ℕ
  small_forward_lower : ℝ
  small_forward_lower_pos : 0 < small_forward_lower
  weighted_forward_lower_to_floor :
    ∀ dst qdst,
      qdst ≤ floor →
        small_forward_lower ≤
          likelihood dst *
            (O.expectedTopSum k dst (qdst + 1) -
              O.expectedTopSum k dst qdst)
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  degree : ℕ
  gap : ℕ → ℕ
  gap_error_tends_to_zero :
    AppliedModelingLib.Math.TendsToZero
      (fun N => ((gap N + 1 : ℕ) : ℝ) / (N : ℝ))
  gap_dominance_eventually :
    ∀ᶠ (N : ℕ) in atTop,
      upper * (N : ℝ) ^ degree * rho ^ (gap N) < lower
  weighted_backward_upper :
    ∀ src qsrc,
      floor < qsrc →
      likelihood src *
          (O.expectedTopSum k src qsrc -
            O.expectedTopSum k src (qsrc - 1)) ≤
        upper * (qsrc : ℝ) ^ degree * rho ^ qsrc
  weighted_forward_lower :
    ∀ dst qdst,
      floor < qdst →
      lower * rho ^ qdst ≤
        likelihood dst *
          (O.expectedTopSum k dst (qdst + 1) -
            O.expectedTopSum k dst qdst)

namespace TopKUniformGeometricTailCertificate

end TopKUniformGeometricTailCertificate

end PRPKG24AccuracyDiversity
