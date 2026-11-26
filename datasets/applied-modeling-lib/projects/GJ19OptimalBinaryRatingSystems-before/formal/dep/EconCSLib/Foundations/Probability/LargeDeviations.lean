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
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Basic
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

open Filter Topology

open scoped BigOperators

namespace EconCSLib

namespace Probability

noncomputable section

/-- Paper-style negative normalized log sequence, `- log(p n) / n`. -/
def logDecay (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  -((n : ℝ)⁻¹) * Real.log (p n)

/-- `p n` has exponential decay rate `rate`. -/
def HasExponentialRate (p : ℕ → ℝ) (rate : ℝ) : Prop :=
  Tendsto (logDecay p) atTop (nhds rate)

namespace HasExponentialRate

end HasExponentialRate

/--
Extended paper-style exponential rate.  A finite real rate is the usual
`HasExponentialRate`; `⊤` records the boundary case where the error
probability is eventually zero, i.e. has infinite exponential rate in the
source convention.
-/
inductive HasExtendedExponentialRate (p : ℕ → ℝ) : WithTop ℝ → Prop
  | finite {rate : ℝ} (h : HasExponentialRate p rate) :
      HasExtendedExponentialRate p rate
  | infinite (hzero : ∀ᶠ n in atTop, p n = 0) :
      HasExtendedExponentialRate p ⊤

namespace HasExtendedExponentialRate

end HasExtendedExponentialRate

/--
Certificate that a nonnegative error probability sequence has a named
exponential decay rate.
-/
structure ExponentialRateCertificate (p : ℕ → ℝ) (rate : ℝ) where
  eventually_pos : ∀ᶠ n in atTop, 0 < p n
  has_rate : HasExponentialRate p rate

/--
Eventual exponential upper bound with an arbitrary positive prefactor:
`p n <= C * exp(-n * rate)` eventually.
-/
def HasExpUpperBoundWithConst (p : ℕ → ℝ) (rate : ℝ) : Prop :=
  ∃ C > 0, ∀ᶠ n in atTop,
    0 ≤ p n ∧ p n ≤ C * Real.exp (-(n : ℝ) * rate)

/--
Eventual exponential lower bound with an arbitrary positive prefactor:
`c * exp(-n * rate) <= p n` eventually.
-/
def HasExpLowerBoundWithConst (p : ℕ → ℝ) (rate : ℝ) : Prop :=
  ∃ c > 0, ∀ᶠ n : ℕ in atTop,
    c * Real.exp (-(n : ℝ) * rate) ≤ p n

namespace HasExpUpperBoundWithConst

end HasExpUpperBoundWithConst

namespace HasExpLowerBoundWithConst

end HasExpLowerBoundWithConst

namespace ExponentialRateCertificate

end ExponentialRateCertificate

/--
Generic finite family of exact error-rate certificates.  This abstracts the
common EC large-deviation pattern before specializing to pairwise ranking
errors: each index has an error probability and an exact exponential rate.
-/
structure FiniteErrorRateCertificate (ι : Type*) where
  errorProb : ι → ℕ → ℝ
  rate : ι → ℝ
  has_rate : ∀ i, ExponentialRateCertificate (errorProb i) (rate i)

namespace FiniteErrorRateCertificate

variable {ι : Type*} [Fintype ι]

end FiniteErrorRateCertificate

/--
Finite family whose components are known relative to a candidate aggregate
rate.  Each component either has some exact finite rate at least `minRate`, or
is eventually zero.  This is the reusable wrapper for mixed finite-rate /
boundary aggregations where a paper wants a finite real rate for the aggregate
without choosing a dummy component rate for eventually-zero terms.
-/
structure FiniteErrorRateEnvelopeCertificate (ι : Type*) (minRate : ℝ) where
  errorProb : ι → ℕ → ℝ
  component :
    ∀ i : ι,
      (∃ rate_i : ℝ,
        minRate ≤ rate_i ∧
          ExponentialRateCertificate (errorProb i) rate_i) ∨
        (∀ᶠ n in atTop, errorProb i n = 0)

namespace FiniteErrorRateEnvelopeCertificate

variable {ι : Type*} [Fintype ι] {minRate : ℝ}

end FiniteErrorRateEnvelopeCertificate

/--
Pairwise ranking-error upper-bound certificate.  `errorProb hi lo n` is the
probability that the pair `(hi, lo)` is misordered after scale `n`; `rate hi lo`
is a certified exponential upper-bound rate.
-/
structure PairwiseErrorUpperBoundCertificate (θ : Type*) where
  errorProb : θ → θ → ℕ → ℝ
  rate : θ → θ → ℝ
  has_bound : ∀ hi lo, HasExpUpperBoundWithConst (errorProb hi lo) (rate hi lo)

namespace PairwiseErrorUpperBoundCertificate

variable {θ : Type*} [Fintype θ]

end PairwiseErrorUpperBoundCertificate

/--
Pairwise ranking-error exact-rate certificate. Unlike
`PairwiseErrorUpperBoundCertificate`, this stores exact normalized-log decay
certificates and can be weakened to any strictly smaller aggregate upper-bound
rate.
-/
structure PairwiseErrorRateCertificate (θ : Type*) where
  errorProb : θ → θ → ℕ → ℝ
  rate : θ → θ → ℝ
  has_rate : ∀ hi lo, ExponentialRateCertificate (errorProb hi lo) (rate hi lo)

namespace PairwiseErrorRateCertificate

variable {θ : Type*} [Fintype θ]

end PairwiseErrorRateCertificate

/--
Pairwise version of `FiniteErrorRateEnvelopeCertificate`.  This keeps the
rating-system and social-choice pairwise APIs aligned with the generic finite
envelope while preserving the paper-facing `hi lo` indexing.
-/
structure PairwiseErrorRateEnvelopeCertificate (θ : Type*) (minRate : ℝ) where
  errorProb : θ → θ → ℕ → ℝ
  component :
    ∀ hi lo : θ,
      (∃ rate_i : ℝ,
        minRate ≤ rate_i ∧
          ExponentialRateCertificate (errorProb hi lo) rate_i) ∨
        (∀ᶠ n in atTop, errorProb hi lo n = 0)

namespace PairwiseErrorRateEnvelopeCertificate

variable {θ : Type*} [Fintype θ] {minRate : ℝ}

end PairwiseErrorRateEnvelopeCertificate

end

end Probability

end EconCSLib
