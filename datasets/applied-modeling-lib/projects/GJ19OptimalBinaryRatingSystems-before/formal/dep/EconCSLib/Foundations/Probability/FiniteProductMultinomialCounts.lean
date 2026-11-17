import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.AffineSpace.Ordered
import Mathlib.Order.Filter.Finite
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Real.Lemmas
import dep.EconCSLib.Foundations.Probability.FiniteExpectation
import dep.EconCSLib.Foundations.Probability.FiniteSupportMGF
import dep.EconCSLib.Foundations.Probability.IIDLargeDeviations
import dep.EconCSLib.Foundations.Probability.LargeDeviations

open scoped BigOperators

open Filter

namespace EconCSLib

namespace Probability

noncomputable section

/--
Checkable lower-bound certificate based on explicit finite bucket partitions.

For each sample size `n`, `bucket n a` assigns coordinates to signal `a`.
The buckets must be a disjoint cover, their weighted counts must force the
left-tail inequality, and the resulting product atom mass must have a
polynomially corrected geometric lower bound.
-/
structure FiniteIidScoreBucketLowerCertificate
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (score : α → ℝ) where
  base : ℝ
  lowerConst : ℝ
  degree : ℕ
  base_pos : 0 < base
  lowerConst_pos : 0 < lowerConst
  bucket : (n : ℕ) → α → Finset (Fin n)
  cover :
    ∀ n : ℕ, ∀ i : Fin n, ∃ a : α, i ∈ bucket n a
  disjoint :
    ∀ n : ℕ, ∀ {a b : α},
      a ≠ b → Disjoint (bucket n a) (bucket n b)
  bucket_tail :
    ∀ n : ℕ,
      ∑ a : α, ((bucket n a).card : ℝ) * score a ≤ 0
  bucket_mass_lower :
    ∀ᶠ n : ℕ in atTop,
      lowerConst * base ^ n / (((n.succ : ℕ) : ℝ) ^ degree) ≤
        ∏ a : α, (μ a).toReal ^ (bucket n a).card

namespace FiniteIidScoreBucketLowerCertificate

/-- The canonical sample selected from a bucket lower certificate. -/
def sample
    {α : Type*} [Fintype α] [DecidableEq α]
    {μ : PMF α} {score : α → ℝ}
    (C : FiniteIidScoreBucketLowerCertificate μ score)
    (n : ℕ) (i : Fin n) : α :=
  Classical.choose (C.cover n i)

/-- The canonical sample selected from a bucket certificate is in the left tail. -/
theorem sample_tail
    {α : Type*} [Fintype α] [DecidableEq α]
    {μ : PMF α} {score : α → ℝ}
    (C : FiniteIidScoreBucketLowerCertificate μ score)
    (n : ℕ) :
    finiteIidScoreSum score (C.sample n) ≤ 0 := sorry

end FiniteIidScoreBucketLowerCertificate

/--
Checkable lower-bound certificate based on explicit empirical count vectors.

This is usually the most convenient finite-type object: for each sample size
`n`, provide counts summing to `n`, prove the count-weighted score lies in the
left tail, and prove a polynomially corrected geometric lower bound on the
product mass of that type.  The sigma-bucket constructor above turns this into
the bucket/path certificates used by exact-rate endpoints.
-/
structure FiniteIidScoreCountVectorLowerCertificate
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (score : α → ℝ) where
  base : ℝ
  lowerConst : ℝ
  degree : ℕ
  base_pos : 0 < base
  lowerConst_pos : 0 < lowerConst
  count : (n : ℕ) → α → ℕ
  count_sum : ∀ n : ℕ, ∑ a : α, count n a = n
  count_tail :
    ∀ n : ℕ, ∑ a : α, (count n a : ℝ) * score a ≤ 0
  count_mass_lower :
    ∀ᶠ n : ℕ in atTop,
      lowerConst * base ^ n / (((n.succ : ℕ) : ℝ) ^ degree) ≤
        ∏ a : α, (μ a).toReal ^ count n a

namespace FiniteIidScoreCountVectorLowerCertificate

end FiniteIidScoreCountVectorLowerCertificate

end

end Probability

end EconCSLib
