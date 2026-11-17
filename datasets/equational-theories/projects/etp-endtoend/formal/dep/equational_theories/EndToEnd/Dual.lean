import Batteries.Data.Array.Lemmas
import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.ToExpr
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Function
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Cases
import dep.equational_theories.EndToEnd.Basic
import dep.equational_theories.EquationLawConversion
import dep.equational_theories.Equations.Basic
import dep.equational_theories.Equations.Command
import dep.equational_theories.Equations.Eqns1000_1999
import dep.equational_theories.Equations.Eqns1_999
import dep.equational_theories.Equations.Eqns2000_2999
import dep.equational_theories.Equations.Eqns3000_3999
import dep.equational_theories.Equations.Eqns4000_4694
import dep.equational_theories.Equations.LawsComplete
import dep.equational_theories.FreeMagma
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw
import dep.equational_theories.MagmaOp
import dep.equational_theories.ParseImplications
import dep.equational_theories.Preorder
import dep.equational_theories.RArray

namespace EndToEnd

open Law

variable {G : Type} [Magma G] {l l' : Law.NatMagmaLaw}

/-- One entry of the duality table: `law` and `dual` are dual to each other. -/
structure DualFact where
  law : Nat
  dual : Nat
  proof : MagmaLaw.IsDual (lawOf law) (lawOf dual)

/-- The dual of law index `n`, according to the table. -/
def dualIdx (dt : RArray DualFact) (n : Nat) : Nat := (dt.get n).dual

/-- The table is indexed by the law it talks about, and stays in range. -/
def checkDualTable (dt : RArray DualFact) (numEq : Nat) : Bool :=
  (List.range numEq).all fun n => ((dt.get n).law == n) && Nat.blt (dt.get n).dual numEq

/-- The dual of a model witness, with the duality supplied by the table.

`hs`/`hr` say the stored dual index lists really are the pointwise duals. They are discharged
by kernel computation, so they cost a constant-size proof term. -/
theorem negFact_dual_table {dt : RArray DualFact} {numEq : Nat}
    (hdt : checkDualTable dt numEq = true) (sat ref sat' ref' : List Nat)
    (hsb : sat.all (fun n => Nat.blt n numEq) = true)
    (hrb : ref.all (fun n => Nat.blt n numEq) = true)
    (hs : sat.map (dualIdx dt) = sat') (hr : ref.map (dualIdx dt) = ref')
    (h : ∃ (G : Type) (_ : Magma G),
          SatisfiesAll G (sat.map lawOf) ∧ RefutesAll G (ref.map lawOf)) :
    ∃ (G : Type) (_ : Magma G),
      SatisfiesAll G (sat'.map lawOf) ∧ RefutesAll G (ref'.map lawOf) := sorry

end EndToEnd
