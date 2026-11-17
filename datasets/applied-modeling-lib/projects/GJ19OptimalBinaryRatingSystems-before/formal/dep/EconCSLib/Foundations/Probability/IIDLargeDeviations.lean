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
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Choose.Sum
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
import dep.EconCSLib.Foundations.Probability.LargeDeviations

open scoped BigOperators

open Filter

namespace EconCSLib

namespace Probability

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Sum of a real-valued score over a finite iid sample. -/
def finiteIidScoreSum {ι : Type*} [Fintype ι]
    (score : α → ℝ) (sample : ι → α) : ℝ :=
  ∑ i : ι, score (sample i)

/-- Left-tail probability for an iid finite sample of size `n`. -/
def finiteIidScoreLeftTailProb
    (μ : PMF α) (score : α → ℝ) (threshold : ℝ) (n : ℕ) : ℝ :=
  pmfProb (pmfProduct (Fin n) α μ)
    (fun sample : Fin n → α => finiteIidScoreSum score sample ≤ threshold)

/--
Checkable lower-bound certificate for finite iid left tails.  A downstream
paper can provide one explicit left-tail sample path for each large `n` whose
product atom mass has the displayed polynomially corrected geometric lower
bound.
-/
structure FiniteIidScorePathLowerCertificate
    (μ : PMF α) (score : α → ℝ) where
  base : ℝ
  lowerConst : ℝ
  degree : ℕ
  base_pos : 0 < base
  lowerConst_pos : 0 < lowerConst
  sample : (n : ℕ) → Fin n → α
  sample_tail :
    ∀ n : ℕ, finiteIidScoreSum score (sample n) ≤ 0
  sample_mass_lower :
    ∀ᶠ n : ℕ in atTop,
      lowerConst * base ^ n / (((n.succ : ℕ) : ℝ) ^ degree) ≤
        (pmfProduct (Fin n) α μ (sample n)).toReal

namespace FiniteIidScorePathLowerCertificate

end FiniteIidScorePathLowerCertificate

/--
Checkable lower-bound certificate for finite iid left tails stated directly at
the tail-probability level.  This is the right target for empirical-type and
multinomial lower bounds, whose exponential contribution includes the number of
samples with a prescribed type rather than just one canonical sample path.
-/
structure FiniteIidScoreTailLowerCertificate
    (μ : PMF α) (score : α → ℝ) where
  base : ℝ
  lowerConst : ℝ
  degree : ℕ
  base_pos : 0 < base
  lowerConst_pos : 0 < lowerConst
  tail_prob_lower :
    ∀ᶠ n : ℕ in atTop,
      lowerConst * base ^ n / (((n.succ : ℕ) : ℝ) ^ degree) ≤
        finiteIidScoreLeftTailProb μ score 0 n

namespace FiniteIidScoreTailLowerCertificate

end FiniteIidScoreTailLowerCertificate

/--
Finite iid Cramer certificate for one score law at the Chernoff exponent
`-inf_z log E exp(z X)`.  This keeps the analytic lower-bound theorem as a
small, reusable boundary while making the downstream exact-rate construction
fully uniform across papers.
-/
structure FiniteIidScoreCramerCertificate
    (μ : PMF α) (score : α → ℝ) where
  eventually_pos :
    ∀ᶠ n in atTop, 0 < finiteIidScoreLeftTailProb μ score 0 n
  upper_bounds :
    ∀ targetRate, targetRate < finiteChernoffRate μ score →
      HasExpUpperBoundWithConst
        (fun n => finiteIidScoreLeftTailProb μ score 0 n) targetRate
  lower_bounds :
    ∀ targetRate, finiteChernoffRate μ score < targetRate →
      HasExpLowerBoundWithConst
        (fun n => finiteIidScoreLeftTailProb μ score 0 n) targetRate

namespace FiniteIidScoreCramerCertificate

end FiniteIidScoreCramerCertificate

end

end Probability

end EconCSLib
