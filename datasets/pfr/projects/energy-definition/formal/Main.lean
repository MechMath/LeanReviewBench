module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Algebra.Order.Sub.Unbundled.Basic
public import Mathlib.Combinatorics.Additive.Convolution
public import Mathlib.Data.Finset.Density
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

open scoped BigOperators Pointwise

public section

variable {G : Type*} [Fintype G] [DecidableEq G]

namespace Finset

section Group

variable [Group G] {s s₁ s₂ t t₁ t₂ : Finset G}

/-- The multiplicative energy `Eₘ[s, t]` of two finsets `s` and `t` in a group is the number of
quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`.

The notation `Eₘ[s, t]` is available in scope `Combinatorics.Additive`. -/
@[expose, to_additive
/-- The additive energy `E[s, t]` of two finsets `s` and `t` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`.

The notation `E[s, t]` is available in scope `Combinatorics.Additive`. -/]
def mulEnergy' (s t : Finset G) : ℚ≥0 :=
  #{x ∈ ((s ×ˢ s) ×ˢ t ×ˢ t) | x.1.1 * x.2.1 = x.1.2 * x.2.2} / Fintype.card G ^ 3

/-- The multiplicative energy of two finsets `s` and `t` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`. -/
scoped[Combinatorics.Additive'] notation3:max "Eₘ[" s ", " t "]" => Finset.mulEnergy' s t

/-- The additive energy of two finsets `s` and `t` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`. -/
scoped[Combinatorics.Additive'] notation3:max "E[" s ", " t "]" => Finset.addEnergy' s t

/-- The multiplicative energy of a finset `s` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × s × s` such that `a₁ * b₁ = a₂ * b₂`. -/
scoped[Combinatorics.Additive'] notation3:max "Eₘ[" s "]" => Finset.mulEnergy' s s

/-- The additive energy of a finset `s` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × s × s` such that `a₁ + b₁ = a₂ + b₂`. -/
scoped[Combinatorics.Additive'] notation3:max "E[" s "]" => Finset.addEnergy' s s

open scoped Combinatorics.Additive'

variable (s t)

variable {s t}

end Group

open scoped Combinatorics.Additive'

section CommGroup

variable [CommGroup G]

end CommGroup

section CommGroup

variable [CommGroup G] (s t : Finset G)

end CommGroup

end Finset
