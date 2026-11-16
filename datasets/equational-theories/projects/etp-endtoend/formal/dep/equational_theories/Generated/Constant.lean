import dep.equational_theories.Magma
import dep.equational_theories.Equations.All
import Mathlib.Tactic

namespace Constant

/- Equational laws that imply the operation is a constant function -/

@[equational_result]
theorem Equation4032_implies_Equation46 (G: Type*) [Magma G] (h: Equation4032 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a, ← h]

end Constant
