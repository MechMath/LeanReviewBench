import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import dep.Covering.FiniteSubGaussianChaining
import dep.Covering.TotalBoundedDudley
import dep.Rademacher.FiniteSample

open Set

open scoped BigOperators Interval

namespace FormalSLT.Covering.UnitIntervalDudley

open FormalSLT.Covering.FiniteSubGaussianChaining

open FormalSLT.Covering.TotalBoundedDudley

open FormalSLT.Rademacher.FiniteSample



noncomputable section

/-- The unit interval as a non-finite metric index type. -/
abbrev UnitInterval : Type :=
  {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}

/-- The Rademacher linear process over the unit interval.

This is the nontrivial follow-on process for the non-finite bridge:
`X(b,t) = signOfBool b * t`.
-/
def unitIntervalRademacherLinearProcess :
    FiniteSubGaussianProcess Bool UnitInterval :=
  { weight := fun _ => (1 : ℝ) / 2
    weight_nonneg := sorry
    weight_sum_one := sorry
    X := fun ω t => signOfBool ω * t.1
    dist := fun s t => dist s t
    dist_nonneg := fun s t => dist_nonneg
    varianceProxy := 1
    varianceProxy_nonneg := sorry
    mgf_increment := sorry }

/-- Supplied supremum functional for the Rademacher linear process over the
unit interval. It is `1` for the positive sign and `0` for the negative sign. -/
def unitIntervalRademacherLinearSup : Bool → ℝ :=
  fun b => if b then 1 else 0

/-- Index type for the first explicit unit-interval mesh sequence: the
three-point half mesh at scale `0`, and the five-point quarter mesh afterward.
-/
private abbrev unitIntervalExplicitMeshIndex : ℕ → Type
  | 0 => Fin 3
  | _ + 1 => Fin 5

private instance unitIntervalExplicitMeshIndex_fintype :
    (j : ℕ) → Fintype (unitIntervalExplicitMeshIndex j)
  | 0 => inferInstance
  | _ + 1 => inferInstance

/-- Product-count envelope for adjacent shifted rounded dyadic grid levels. -/
def unitIntervalRoundedDyadicGridCoverCount (j : ℕ) : ℕ :=
  (2 ^ (j + 1) + 1) * (2 ^ (j + 2) + 1)

end

end FormalSLT.Covering.UnitIntervalDudley
