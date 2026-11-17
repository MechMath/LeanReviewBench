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
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Order.Compact
import dep.AppliedModelingLib.Foundations.Probability.PMFKernel

open scoped BigOperators

namespace AppliedModelingLib

/--
A finite integer allocation over a finite class/type space `κ`.

This is the common representation behind the recommendation-diversity paper:
`count k` is the number of recommended items of type `k`.
-/
structure Allocation (κ : Type*) where
  count : κ → ℕ

namespace Allocation

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Total number of allocated units. -/
def total (a : Allocation κ) : ℕ :=
  ∑ k, a.count k

/-- `a` is an allocation of exactly `N` units. -/
def HasTotal (a : Allocation κ) (N : ℕ) : Prop :=
  a.total = N

/-- Weighted finite objective over allocation counts. -/
noncomputable def objective
    (a : Allocation κ) (weight : κ → ℝ) (valueOfCount : κ → ℕ → ℝ) : ℝ :=
  ∑ k, weight k * valueOfCount k (a.count k)

/-- Marginal value of increasing a count from `q` to `q + 1`. -/
noncomputable def marginal (valueOfCount : κ → ℕ → ℝ) (k : κ) (q : ℕ) : ℝ :=
  valueOfCount k (q + 1) - valueOfCount k q

/-- Weighted forward marginal gain from adding one unit to coordinate `k`. -/
noncomputable def weightedForwardMarginal
    (weight : κ → ℝ) (valueOfCount : κ → ℕ → ℝ) (k : κ) (q : ℕ) : ℝ :=
  weight k * marginal valueOfCount k q

/--
Weighted value lost by removing the `q`-th unit from coordinate `k`.

The value is set to `0` at `q = 0`; exchange theorems that model an actual
transfer separately assume `CanMoveOne a k`.
-/
noncomputable def weightedBackwardMarginal
    (weight : κ → ℝ) (valueOfCount : κ → ℕ → ℝ) (k : κ) (q : ℕ) : ℝ :=
  if h : q = 0 then 0 else weight k * (valueOfCount k q - valueOfCount k (q - 1))

/-- `a` maximizes a weighted separable count objective among allocations of total `N`. -/
def IsOptimalAtTotal
    (weight : κ → ℝ) (valueOfCount : κ → ℕ → ℝ)
    (N : ℕ) (a : Allocation κ) : Prop :=
  HasTotal a N ∧
    ∀ b : Allocation κ, HasTotal b N →
      objective b weight valueOfCount ≤ objective a weight valueOfCount

end Allocation

end AppliedModelingLib

namespace AppliedModelingLib

namespace Allocation

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/--
Finite code for allocations of exactly `N` units.

Each coordinate is stored as a `Fin (N + 1)`, and the subtype proof records
that the decoded allocation has total `N`.
-/
abbrev FeasibleCode (κ : Type*) [Fintype κ] (N : ℕ) :=
  { f : κ → Fin (N + 1) // ∑ k : κ, (f k).val = N }

namespace FeasibleCode

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

end FeasibleCode

end Allocation

end AppliedModelingLib
