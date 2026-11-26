import Init.Data.Int.DivMod.Lemmas
import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Data.ENat.Basic
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Set.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Zify
import dep.equational_theories.EquationLawConversion
import dep.equational_theories.Equations.Command
import dep.equational_theories.Equations.Eqns1000_1999
import dep.equational_theories.FreeMagma
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw
import dep.equational_theories.MagmaOp
import dep.equational_theories.ParseImplications
import dep.equational_theories.Preorder

namespace FullSpectrum

abbrev EqFullSpectrum (Eq : (G: Type) -> (_: Magma G) -> Prop) :=
  ∀ n : ℕ, ∃ (M : Magma (Fin n)), Eq (Fin n) M

syntax "HasFullSpectrum" "[" num,* "]" : term

open Lean Meta Elab Term Tactic Parser.Term in
elab_rules : term | `(HasFullSpectrum [ $eqs,* ]) => do
  let s := eqs.getElems.map fun ⟨s⟩ =>
    mkApp (mkConst ``EqFullSpectrum) (mkConst (.mkSimple s!"Equation{s.toNat}") [0])
  let e := mkAndN s.toList
  return e

syntax "NotFullSpectrum" "[" num,* "]" : term

open Lean Meta Elab Term Tactic Parser.Term in
elab_rules : term | `(NotFullSpectrum [ $eqs,* ]) => do
  let s := eqs.getElems.map fun ⟨s⟩ =>
    mkApp (mkConst ``Not)
      (mkApp (mkConst ``EqFullSpectrum) (mkConst (.mkSimple s!"Equation{s.toNat}") [0]))
  let e := mkAndN s.toList
  return e

theorem full_spectrum_Equation1482 : HasFullSpectrum [1482] := sorry

end FullSpectrum
