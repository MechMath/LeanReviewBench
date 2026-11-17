import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Basic
import Mathlib.LinearAlgebra.AffineSpace.Ordered
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Union
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.UniformSpace.UniformConvergence
import dep.EconCSLib.Foundations.Math.FiniteOptimization
import dep.EconCSLib.Foundations.Optimization.Certificate
import dep.EconCSLib.Foundations.Probability.BinaryRatingLDP
import dep.EconCSLib.Foundations.Probability.FiniteExpectation
import dep.EconCSLib.Foundations.Probability.FiniteMeasurablePartition
import dep.EconCSLib.Foundations.Probability.FiniteProductMultinomialCounts
import dep.EconCSLib.Foundations.Probability.FiniteRankingEvents
import dep.EconCSLib.Foundations.Probability.FiniteRatingComparison
import dep.EconCSLib.Foundations.Probability.FiniteSupportMGF
import dep.EconCSLib.Foundations.Probability.IIDLargeDeviations
import dep.EconCSLib.Foundations.Probability.IndependentProduct
import dep.EconCSLib.Foundations.Probability.IntegralLargeDeviations
import dep.EconCSLib.Foundations.Probability.LargeDeviations

open scoped BigOperators

namespace GJ19OptimalBinaryRatingSystems

noncomputable section

open EconCSLib.Probability

open Filter Topology

open MeasureTheory

/-- Lower endpoint index for adjacent intervals in a finite binary level chain. -/
abbrev adjacentLowIndex {m : ℕ} (i : Fin (m + 1)) : Fin (m + 2) :=
  Fin.castSucc i

/-- Upper endpoint index for adjacent intervals in a finite binary level chain. -/
abbrev adjacentHighIndex {m : ℕ} (i : Fin (m + 1)) : Fin (m + 2) :=
  i.succ

/-- First level in the finite binary chain. -/
abbrev firstLevelIndex {m : ℕ} : Fin (m + 2) :=
  ⟨0, sorry⟩

/-- Last level in the finite binary chain. -/
abbrev lastLevelIndex {m : ℕ} : Fin (m + 2) :=
  ⟨m + 1, sorry⟩

/--
Endpoint-aware adjacent rate for a finite binary level chain with source
endpoint convention `t_0 = 0`, `t_last = 1`.  The first and last comparisons
use the simplified endpoint rates; middle comparisons use the closed weighted
Bernoulli rate.
-/
def binaryEndpointAwareAdjacentRate {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (i : Fin (m + 1)) : ℝ :=
  if i.val = 0 then
    sampleRate (adjacentHighIndex i) *
      (-Real.log (1 - successProb (adjacentHighIndex i)))
  else if i.val = m then
    sampleRate (adjacentLowIndex i) *
      (-Real.log (successProb (adjacentLowIndex i)))
  else
    weightedBernoulliClosedThresholdRate
      (sampleRate (adjacentHighIndex i))
      (sampleRate (adjacentLowIndex i))
      (successProb (adjacentHighIndex i))
      (successProb (adjacentLowIndex i))

/--
The nontrivial ordered level pairs used in the C.3/Theorem 3.1 decomposition:
strictly ordered level indices, excluding the single bottom-to-top endpoint
comparison.
-/
def theorem31OrderedNontrivialPairSelected {m : ℕ}
    (piece : Fin (m + 2) × Fin (m + 2)) : Prop :=
  piece.1.val + 1 ≤ piece.2.val ∧
    (piece.1.val ≠ 0 ∨ piece.2.val ≠ m + 1)

instance theorem31OrderedNontrivialPairSelected_decidablePred {m : ℕ} :
    DecidablePred (theorem31OrderedNontrivialPairSelected (m := m)) := by
  intro piece
  dsimp [theorem31OrderedNontrivialPairSelected]
  infer_instance

/-- Subtype of nontrivial ordered level pairs used by Theorem 3.1/C.3. -/
abbrev theorem31OrderedNontrivialPairComponent (m : ℕ) :=
  {piece : Fin (m + 2) × Fin (m + 2) //
    theorem31OrderedNontrivialPairSelected (m := m) piece}

/--
Feasible finite endpoint level vector for Lemma 3.1: the source convention
fixes the first level at `0`, the last at `1`, and adjacent levels strictly
increase.
-/
def BinaryEndpointLevelVector {m : ℕ} (t : Fin (m + 2) → ℝ) : Prop :=
  t (firstLevelIndex : Fin (m + 2)) = 0 ∧
    t (lastLevelIndex : Fin (m + 2)) = 1 ∧
    ∀ i : Fin (m + 1), t (adjacentLowIndex i) < t (adjacentHighIndex i)

/-- Every level of an endpoint level vector is nonnegative. -/
theorem BinaryEndpointLevelVector_nonneg {m : ℕ}
    {t : Fin (m + 2) → ℝ} (ht : BinaryEndpointLevelVector t)
    (i : Fin (m + 2)) :
    0 ≤ t i := sorry

/-- Every level of an endpoint level vector is at most one. -/
theorem BinaryEndpointLevelVector_le_one {m : ℕ}
    {t : Fin (m + 2) → ℝ} (ht : BinaryEndpointLevelVector t)
    (i : Fin (m + 2)) :
    t i ≤ 1 := sorry

/-- Finite worst-adjacent endpoint-aware rate for a binary level chain. -/
def binaryEndpointAwareAdjacentRateObjective {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ) : ℝ :=
  EconCSLib.finiteMin (binaryEndpointAwareAdjacentRate successProb sampleRate)

/-- Endpoint-aware adjacent rates equalize to one common value. -/
def BinaryEndpointAwareAdjacentRatesEqualize {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ) : Prop :=
  ∀ i j : Fin (m + 1),
    binaryEndpointAwareAdjacentRate successProb sampleRate i =
      binaryEndpointAwareAdjacentRate successProb sampleRate j

/-- Source finite binary-rating model from success probabilities. -/
abbrev binaryRatingModel {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1) :
    FiniteRatingLDPModel Seller Bool :=
  realBinaryRatingLDPModel successProb hprob0 hprob1

/--
Theorem 3.1/C.3 ordered quality partition: monotone cutpoints split the
continuum quality interval into the half-open cells used by a stepwise binary
rating rule.
-/
def theorem31_ordered_quality_interval_partition
    (μ : Measure ℝ) (n : ℕ) (cut : ℕ → ℝ) (hmono : Monotone cut) :
    FiniteMeasurableSetPartition μ (Fin n) :=
  FiniteMeasurableSetPartition.orderedRealIocNatCutpoints μ n cut hmono

/--
Theorem 3.1/C.3 ordered quality-pair partition: selected products of ordered
quality cells give the finite rectangle family used to decompose the pairwise
continuum error integral.
-/
def theorem31_ordered_quality_pair_partition
    (μ : Measure ℝ) (n : ℕ) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (selected : Fin n × Fin n → Prop) [DecidablePred selected] :
    FiniteMeasurableSetPartition (μ.prod μ)
      {piece : Fin n × Fin n // selected piece} :=
  (theorem31_ordered_quality_interval_partition μ n cut hmono).selectedProduct
    (theorem31_ordered_quality_interval_partition μ n cut hmono) selected

/--
Canonical interior point of a selected ordered pair cell, obtained by taking
the midpoint of each coordinate interval.
-/
def theorem31_ordered_quality_pair_component_midpoint {m : ℕ}
    (cut : ℕ → ℝ) (component : theorem31OrderedNontrivialPairComponent m) :
    ℝ × ℝ :=
  FiniteMeasurableSetPartition.orderedRealIocNatCutpointsProdMidpoint
    cut cut component.val

/--
Source-defined `Wbar_k` convention for Theorem 3.1's fixed-discretization
ordered-rectangle branch: integrate the selected piecewise-constant error
kernel over the source's ordered quality-pair partition.
-/
def theorem31SourceWbar
    (μ : Measure ℝ) {m : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (sampleRate : Fin (m + 2) → ℝ)
    (levels : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector levels)
    (weight : ℝ × ℝ → ℝ) : ℕ → ℝ :=
  fun k : ℕ =>
    ∫ x in
      (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
        (theorem31OrderedNontrivialPairSelected (m := m))).support,
      weight x *
        (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
          (theorem31OrderedNontrivialPairSelected (m := m))).piecewiseConstKernel
            (fun component k =>
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel levels
                  (BinaryEndpointLevelVector_nonneg hlevels)
                  (BinaryEndpointLevelVector_le_one hlevels))
                sampleRate component.val.2 component.val.1 k)
            k x ∂(μ.prod μ)

end

end GJ19OptimalBinaryRatingSystems
