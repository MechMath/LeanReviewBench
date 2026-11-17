import Lean
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Equiv.Basic
import dep.equational_theories.EquationLawConversion
import dep.equational_theories.Equations.Command
import dep.equational_theories.FreeMagma
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw

abbrev Equation345169.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y))
        (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z y)))
