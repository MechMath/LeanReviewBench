import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

namespace EconCSLib

namespace Optimization

/-- `x` maximizes `objective` over the feasible region. -/
def IsMaximizerOn {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (x : α) : Prop :=
  feasible x ∧ ∀ y, feasible y → objective y ≤ objective x

/-- `x` minimizes `objective` over the feasible region. -/
def IsMinimizerOn {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (x : α) : Prop :=
  feasible x ∧ ∀ y, feasible y → objective x ≤ objective y

/-- Strict sufficient condition for a unique maximizer. -/
def IsStrictMaximizerOn {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (x : α) : Prop :=
  feasible x ∧ ∀ y, feasible y → y ≠ x → objective y < objective x

/-- Strict sufficient condition for a unique minimizer. -/
def IsStrictMinimizerOn {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (x : α) : Prop :=
  feasible x ∧ ∀ y, feasible y → y ≠ x → objective x < objective y

namespace IsMaximizerOn

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {x y : α}

/-- A maximizer upper-bounds every feasible objective value. -/
theorem le (h : IsMaximizerOn feasible objective x)
    (hy : feasible y) : objective y ≤ objective x := sorry

end IsMaximizerOn

namespace IsMinimizerOn

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {x y : α}

/-- A minimizer lower-bounds every feasible objective value. -/
theorem le (h : IsMinimizerOn feasible objective x)
    (hy : feasible y) : objective x ≤ objective y := sorry

end IsMinimizerOn

namespace IsStrictMaximizerOn

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {x y : α}

end IsStrictMaximizerOn

namespace IsStrictMinimizerOn

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {x y : α}

end IsStrictMinimizerOn

/--
A maximization certificate: the candidate is feasible, has value `value`, and
`value` upper-bounds every feasible objective value.
-/
structure UpperBoundCertificate {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (value : ℝ) where
  candidate : α
  candidate_feasible : feasible candidate
  candidate_value : objective candidate = value
  upper_bound : ∀ y, feasible y → objective y ≤ value

/--
A minimization certificate: the candidate is feasible, has value `value`, and
`value` lower-bounds every feasible objective value.
-/
structure LowerBoundCertificate {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (value : ℝ) where
  candidate : α
  candidate_feasible : feasible candidate
  candidate_value : objective candidate = value
  lower_bound : ∀ y, feasible y → value ≤ objective y

/-- A strict maximization certificate proving uniqueness by strict upper bounds. -/
structure StrictUpperBoundCertificate {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (value : ℝ) where
  candidate : α
  candidate_feasible : feasible candidate
  candidate_value : objective candidate = value
  strict_upper_bound : ∀ y, feasible y → y ≠ candidate → objective y < value

/-- A strict minimization certificate proving uniqueness by strict lower bounds. -/
structure StrictLowerBoundCertificate {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (value : ℝ) where
  candidate : α
  candidate_feasible : feasible candidate
  candidate_value : objective candidate = value
  strict_lower_bound : ∀ y, feasible y → y ≠ candidate → value < objective y

namespace UpperBoundCertificate

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {value : ℝ}

end UpperBoundCertificate

namespace LowerBoundCertificate

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {value : ℝ}

end LowerBoundCertificate

namespace StrictUpperBoundCertificate

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {value : ℝ}

end StrictUpperBoundCertificate

namespace StrictLowerBoundCertificate

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {value : ℝ}

end StrictLowerBoundCertificate

end Optimization

end EconCSLib
