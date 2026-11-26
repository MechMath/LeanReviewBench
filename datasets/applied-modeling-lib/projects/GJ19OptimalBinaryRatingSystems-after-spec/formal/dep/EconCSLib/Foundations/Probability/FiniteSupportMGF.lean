import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.Ordered
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import dep.EconCSLib.Foundations.Probability.FiniteExpectation

open scoped BigOperators Topology

open Filter

namespace EconCSLib

namespace Probability

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Finite moment-generating function for a real score under a finite PMF. -/
def finiteMGF (μ : PMF α) (score : α → ℝ) (z : ℝ) : ℝ :=
  ∑ a : α, (μ a).toReal * Real.exp (z * score a)

/-- Finite log moment-generating function. -/
def finiteLogMGF (μ : PMF α) (score : α → ℝ) (z : ℝ) : ℝ :=
  Real.log (finiteMGF μ score z)

/-- Legendre-transform objective at a fixed dual parameter `z`. -/
def finiteLegendreValue (μ : PMF α) (score : α → ℝ)
    (a z : ℝ) : ℝ :=
  z * a - finiteLogMGF μ score z

/--
Finite-support Cramer-style rate function written as the supremum of the
Legendre objective.
-/
def finiteRateFunction (μ : PMF α) (score : α → ℝ)
    (a : ℝ) : ℝ :=
  sSup (Set.range fun z : ℝ => finiteLegendreValue μ score a z)

/--
Finite-support Chernoff exponent for the left-tail event of a score with
positive mean, written as `- inf_z log E exp(z X)`. The actual tail theorem is
supplied by a caller-provided LDP/Chernoff certificate; this definition fixes
the reusable finite-support formula.
-/
def finiteChernoffRate (μ : PMF α) (score : α → ℝ) : ℝ :=
  -sInf (Set.range fun z : ℝ => finiteLogMGF μ score z)

/--
Finite signal model for pairwise score-gap LDP calculations, e.g. election
papers comparing the two candidates' per-voter score contributions under a
single finite law.
-/
structure FiniteScoreGapLDPModel (Signal : Type*) [Fintype Signal]
    [DecidableEq Signal] where
  law : PMF Signal
  hiScore : Signal → ℝ
  loScore : Signal → ℝ

namespace FiniteScoreGapLDPModel

variable {Signal : Type*} [Fintype Signal] [DecidableEq Signal]

def gapScore (M : FiniteScoreGapLDPModel Signal) (s : Signal) : ℝ :=
  M.hiScore s - M.loScore s

def logMGF (M : FiniteScoreGapLDPModel Signal) (z : ℝ) : ℝ :=
  finiteLogMGF M.law M.gapScore z

end FiniteScoreGapLDPModel

/--
Finite rating-scale model for large-deviation calculations.  `typeLaw θ` is
the rating distribution for a seller/item of latent type `θ`, and `score`
assigns a real-valued score to each rating category.
-/
structure FiniteRatingLDPModel (θ Rating : Type*) [Fintype Rating]
    [DecidableEq Rating] where
  typeLaw : θ → PMF Rating
  score : Rating → ℝ

namespace FiniteRatingLDPModel

variable {θ Rating : Type*} [Fintype Rating] [DecidableEq Rating]

def logMGF (M : FiniteRatingLDPModel θ Rating) (t : θ) (z : ℝ) : ℝ :=
  finiteLogMGF (M.typeLaw t) M.score z

def rateFunction (M : FiniteRatingLDPModel θ Rating)
    (t : θ) (a : ℝ) : ℝ :=
  finiteRateFunction (M.typeLaw t) M.score a

def pairwiseRateObjective (M : FiniteRatingLDPModel θ Rating)
    (sampleRate : θ → ℝ) (hi lo : θ) (a : ℝ) : ℝ :=
  sampleRate hi * M.rateFunction hi a +
    sampleRate lo * M.rateFunction lo a

/--
Pairwise threshold rate for comparing two finite-rating populations, before a
paper supplies the analytic large-deviation certificate.
-/
def pairwiseThresholdRate (M : FiniteRatingLDPModel θ Rating)
    (sampleRate : θ → ℝ) (hi lo : θ) : ℝ :=
  sInf (Set.range fun a : ℝ =>
    M.pairwiseRateObjective sampleRate hi lo a)

/--
A finite rating law places positive mass on both sides of a threshold score.
This is the reusable nondegeneracy condition used by finite empirical-type
Cramer lower bounds in rating-system papers.
-/
def straddlesThreshold (M : FiniteRatingLDPModel θ Rating)
    (t : θ) (a : ℝ) : Prop :=
  (∃ rBelow : Rating, 0 < (M.typeLaw t rBelow).toReal ∧ M.score rBelow < a) ∧
    (∃ rAbove : Rating, 0 < (M.typeLaw t rAbove).toReal ∧ a < M.score rAbove)

end FiniteRatingLDPModel

end

end Probability

end EconCSLib
