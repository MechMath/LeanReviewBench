module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Group.Pointwise.Finset.Density
public import Mathlib.Algebra.Group.Translate
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Algebra.Order.Sub.Unbundled.Basic
public import Mathlib.Algebra.Star.Conjneg
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.NNReal.Star
public import Mathlib.Combinatorics.Additive.Convolution
public import Mathlib.Data.Finset.Density
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

public section

open Finset Fintype Function

open scoped BigOperators ComplexConjugate NNReal Pointwise translate

local notation a " /ℚ " q => (q : ℚ≥0)⁻¹ • a

variable {G H K L : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

section Semifield

variable [Semifield K] [CharZero K] {f g : G → K}

/-- Compact convolution on a finite group.

The value of `f ∗ g` at `a` is the average of the value of `f b * g c` over `b + c = a`. -/
@[expose] def conv (f g : G → K) : G → K := fun a ↦ 𝔼 x : G × G with x.1 + x.2 = a, f x.1 * g x.2

@[inherit_doc] infixl:71 " ∗ " => conv

variable [StarRing K]

/-- Compact difference convolution on a finite group.

The value of `f ∗ g` at `a` is the average of the value of `f b * g c` over `b - c = a`. -/
@[expose]
def dconv (f g : G → K) : G → K := fun a ↦ 𝔼 x : G × G with x.1 - x.2 = a, f x.1 * conj g x.2

@[inherit_doc] infixl:71 " ○ " => dconv

end Semifield

section Field

variable [Field K] [CharZero K]

variable [StarRing K]

end Field

namespace RCLike

variable {𝕜 : Type} [RCLike 𝕜] (f g : G → ℝ) (a : G)

end RCLike

namespace Complex

variable (f g : G → ℝ) (a : G)

end Complex

namespace NNReal

variable (f g : G → ℝ≥0) (a : G)

end NNReal
