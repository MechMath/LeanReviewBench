import Batteries.Tactic.Exact
import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Order.BooleanAlgebra.Set
import Qq
import dep.equational_theories.EquationLawConversion
import dep.equational_theories.Equations.Basic
import dep.equational_theories.Equations.Command
import dep.equational_theories.FreeMagma
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw
import dep.equational_theories.ParseImplications
import dep.equational_theories.Preorder
import dep.equational_theories.ShefferAlgebra

namespace Sheffer

open Sheffer

instance (B : Type*) [BooleanAlgebra B] : Magma B where
  op a b := (a ⊓ b)ᶜ

theorem Sheffer_Equation345169 (B : Type*) [BooleanAlgebra B] : Equation345169 B := sorry

theorem Equation345169_implies_Axiom1 (G : Type*) [Magma G] (h : Equation345169 G) :
    ∀ x : G, x = (x ◇ x) ◇ (x ◇ x) := sorry

theorem Equation345169_implies_Axiom2 (G : Type*) [Magma G] (h : Equation345169 G) :
    ∀ x y : G, x ◇ x = x ◇ (y ◇ (y ◇ y)):= sorry

theorem Equation345169_implies_Axiom3 (G : Type*) [Magma G] (h : Equation345169 G) :
    ∀ x y z : G, (x ◇ (y ◇ z)) ◇ (x ◇ (y ◇ z)) = ((y ◇ y) ◇ x) ◇ ((z ◇ z) ◇ x):= sorry

@[instance_reducible] def Equation345169_is_Sheffer (G : Type*) [m : Magma G]
  (h : Equation345169 G) [Inhabited G] :
    ShefferAlgebra G :=
  let sh₁ x := x |> Equation345169_implies_Axiom1 G h |> Eq.symm
  let sh₂ x y := Equation345169_implies_Axiom2 G h x y |> Eq.symm
  let sh₃ x y z := Equation345169_implies_Axiom3 G h x y z
  let _ : Stroke G := ⟨ m.op ⟩
  ShefferAlgebra.mk default sh₁ sh₂ sh₃

@[instance_reducible] def Equation345169_is_Boolean (G : Type*) [Magma G]
  (h : Equation345169 G) [Inhabited G] :
    BooleanAlgebra G :=
  let _ := Equation345169_is_Sheffer G h
  @ShefferToBooleanAlg G _

end Sheffer
