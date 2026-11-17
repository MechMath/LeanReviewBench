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
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Order.Filter.Finite
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import dep.EconCSLib.Foundations.Probability.FiniteExpectation
import dep.EconCSLib.Foundations.Probability.FiniteSupportMGF
import dep.EconCSLib.Foundations.Probability.LargeDeviations

open Filter Topology MeasureTheory

namespace EconCSLib

namespace Probability

noncomputable section

/--
Real-valued essential-infimum interface tailored to Laplace-principle proofs.

`HasAEEssentialInfimum μ phi rate` records the two mathematical facts needed
from the statement “`rate` is the essential infimum of `phi`”: `rate` is an
almost-everywhere lower bound, and every strict near-sublevel has positive
real measure.
-/
def HasAEEssentialInfimum
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (phi : α → ℝ) (rate : ℝ) : Prop :=
  (∀ᵐ x ∂μ, rate ≤ phi x) ∧
    ∀ ε > 0, ∃ s : Set α,
      MeasurableSet s ∧
        0 < μ.real s ∧
          ∀ x, x ∈ s → phi x ≤ rate + ε

/--
Positive-weight near-essential-infimum interface for weighted Laplace
principles.  For every strict neighborhood of the essential infimum, there is
a positive-measure restricted set on which the weight is uniformly positive
and the rate function is within that neighborhood.
-/
def HasPositiveWeightNearAEEssentialInfimum
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w phi : α → ℝ) (rate : ℝ) : Prop :=
  ∀ ε > 0, ∃ s : Set α, ∃ c : ℝ,
    0 < μ.real s ∧ 0 < c ∧
      ∀ᵐ x ∂μ.restrict s, c ≤ w x ∧ phi x ≤ rate + ε

namespace HasAEEssentialInfimum

end HasAEEssentialInfimum

namespace HasPositiveWeightNearAEEssentialInfimum

end HasPositiveWeightNearAEEssentialInfimum

/--
Source-style normalized logarithmic rate of a positive kernel.  The value at
`n = 0` is arbitrary; all large-deviation uses are eventual in `n`.
-/
def normalizedLogKernelRate
    {α : Type*} (F : ℕ → α → ℝ) (n : ℕ) (x : α) : ℝ :=
  if n = 0 then 0 else -Real.log (F n x) / (n : ℝ)

/--
Uniform-on-set exponential-rate certificate for a source-shaped kernel.  The
constant prefactors are allowed because they disappear after normalizing
`-log` by the sample size.
-/
structure UniformExponentialRateCertificateOn
    {α : Type*} (F : ℕ → α → ℝ) (rate : α → ℝ) (s : Set α) where
  lowerConst : ℝ
  upperConst : ℝ
  lowerConst_pos : 0 < lowerConst
  upperConst_pos : 0 < upperConst
  lower :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ x : α, x ∈ s →
        lowerConst * Real.exp (-(n : ℝ) * (rate x + ε)) ≤ F n x
  upper :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ x : α, x ∈ s →
        F n x ≤ upperConst * Real.exp (-(n : ℝ) * (rate x - ε))

/--
Uniform-on-set normalized-log large-deviation certificate for a source-shaped
kernel.  This is the most direct form of assumptions such as
`-log F_n(x) / n -> rate x` uniformly on a compact parameter set.
-/
structure UniformNormalizedLogRateCertificateOn
    {α : Type*} (F : ℕ → α → ℝ) (rate : α → ℝ) (s : Set α) where
  eventually_pos :
    ∀ᶠ n : ℕ in atTop, ∀ x : α, x ∈ s → 0 < F n x
  uniform :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ x : α, x ∈ s →
        |normalizedLogKernelRate F n x - rate x| ≤ ε

namespace UniformExponentialRateCertificateOn

/--
The lower half of a uniform exponential sandwich gives eventual positivity on
the certified set.
-/
theorem eventually_pos
    {α : Type*} {F : ℕ → α → ℝ} {rate : α → ℝ} {s : Set α}
    (C : UniformExponentialRateCertificateOn F rate s) :
    ∀ᶠ n : ℕ in atTop, ∀ x : α, x ∈ s → 0 < F n x := sorry

end UniformExponentialRateCertificateOn

namespace UniformNormalizedLogRateCertificateOn

end UniformNormalizedLogRateCertificateOn

end

end Probability

end EconCSLib
