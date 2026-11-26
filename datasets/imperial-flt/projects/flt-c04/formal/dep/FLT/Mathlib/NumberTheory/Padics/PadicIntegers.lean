module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.RingHoms

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Function Topology Subgroup

open scoped NNReal nonZeroDivisors Pointwise

variable {p : ℕ} [Fact p.Prime]

namespace PadicInt

variable {x : ℤ_[p]}

attribute [simp] coe_eq_zero

lemma coe_injective : Injective ((↑) : ℤ_[p] → ℚ_[p]) := sorry

instance : Infinite ℤ_[p] := sorry

noncomputable instance : Coe ℤ_[p]ˣ ℚ_[p]ˣ where coe := Units.map Coe.ringHom.toMonoidHom

noncomputable instance : Coe ℤ_[p]⁰ ℚ_[p]ˣ where
  coe x := .mk0 x.1 <| map_ne_zero_of_mem_nonZeroDivisors (M₀ := ℤ_[p])
    Coe.ringHom coe_injective x.2

end PadicInt

namespace Padic

end Padic
