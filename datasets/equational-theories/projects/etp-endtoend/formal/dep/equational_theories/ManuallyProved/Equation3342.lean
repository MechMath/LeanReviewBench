import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Units
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import dep.equational_theories.EquationLawConversion
import dep.equational_theories.Equations.Basic
import dep.equational_theories.Equations.Command
import dep.equational_theories.Equations.Eqns1000_1999
import dep.equational_theories.Equations.Eqns1_999
import dep.equational_theories.Equations.Eqns2000_2999
import dep.equational_theories.Equations.Eqns3000_3999
import dep.equational_theories.Equations.Eqns4000_4694
import dep.equational_theories.FactsSyntax
import dep.equational_theories.FreeMagma
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw
import dep.equational_theories.MagmaOp
import dep.equational_theories.ParseImplications
import dep.equational_theories.Preorder

namespace Eq3342

def op (a b : Option (ℕ × ℕ)) : Option (ℕ × ℕ) :=
  match a, b with
  | some (a, b),  some (c, d) =>
    if b = d ∧ (a = c ∨ a + 1 = c) then (0, b + 1) else
    if b + 1 = d ∧ a ≥ c then (a-c+1, b) else
    if b = d + 1 ∧ a < c then (c-a, d) else
    none
  | _, _ => none

end Eq3342
