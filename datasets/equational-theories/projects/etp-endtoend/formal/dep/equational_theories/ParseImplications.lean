import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Equiv.Basic
import dep.equational_theories.FreeMagma
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw
import dep.equational_theories.Preorder

open Lean Qq

/--
Names of equations satisfied rsp. refuted by the same magma; used to concisely express
antiimplications.

For example, if `satisfied = [1, 2]` and `refuted = [4, 5]`, then this expresses
the four antiimplications `¬ 1→4`, `¬ 1→5`, `¬ 2→4`, `¬ 2→5`.
-/
structure Facts where
  satisfied : Array String
  refuted : Array String
  /-- Is this result marked with the Finite typeclass? -/
  finite : Bool
deriving Lean.ToJson, Lean.FromJson, Inhabited

/--
Extracts the equation name out of an expression of the form `EquationN G inst`.
-/
def getEquationName (app : Expr) : Option String := do
  match app with
  | (.app (.app (.const name _) _) _) =>
    -- Copy the string to allow it to safely escape from `Lean.withImportModules`.
    -- Otherwise, segfaults are possible.
    let copy := name.toString
    if copy.startsWith "Equation" then
      some ("" ++ copy)
    else
      none
  | _ => none

def getEquationNumber (app : Expr) : Option Nat := do
  let nm ← getEquationName app
  nm.replace "Equation" "" |>.toNat?
