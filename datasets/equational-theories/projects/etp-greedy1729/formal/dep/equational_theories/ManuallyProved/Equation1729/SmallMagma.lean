import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.Data.Countable.Defs
import Mathlib.Data.DFinsupp.Encodable
import Mathlib.Data.Finset.Union
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Preorder.Chain
import Mathlib.RepresentationTheory.Basic
import Mathlib.Tactic
import dep.equational_theories.EquationLawConversion
import dep.equational_theories.Equations.Basic
import dep.equational_theories.Equations.Command
import dep.equational_theories.Equations.Eqns1000_1999
import dep.equational_theories.FreeMagma
import dep.equational_theories.FreshGenerator
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw
import dep.equational_theories.ParseImplications
import dep.equational_theories.Preorder

namespace Eq1729

abbrev SM := DirectSum ℕ (fun _ ↦ ZMod 4)

open AddToMagma

instance SM_countable : Countable SM := sorry

abbrev E (n:ℕ) : SM := (DirectSum.of (fun _ ↦ ZMod 4) n) 1

def S (a : SM) := a ◇ a

abbrev N := FreeGroup SM

instance N_countable : Countable N := sorry

abbrev e (a:SM) := FreeGroup.of a

/-- Impose an order on N: x ≤ y if x is a right subword of y  (or equivalently, x is on the unique
simple path from 1 to y).  The spelling may not be optimal. -/
instance N_LE : LE N where
  le x y := x.toWord <:+ y.toWord

instance N_order : PartialOrder N where
  le := N_LE.le
  le_refl _ := List.suffix_rfl
  le_trans _ _ _ := List.IsSuffix.trans
  le_antisymm x y hxy hyx := FreeGroup.toWord_injective <|
    List.IsSuffix.eq_of_length_le hxy (List.IsSuffix.length_le hyx)

instance : WellFoundedLT N := sorry

instance : LocallyFiniteOrderBot N := LocallyFiniteOrderBot.ofIic
  (finsetIic := fun x => (List.map (FreeGroup.mk) x.toWord.tails).toFinset)
  (mem_Iic := fun a x => sorry)

/-- the parent of x is defined to be the unique element adjacent to x whose reduced word is shorter, with the junk convention that the parent of the identity is itself -/
def parent (x : N) : N := FreeGroup.mk x.toWord.tail

theorem parent_le (x : N) : parent x ≤ x := sorry

theorem lt_iff_le_parent {x y : N} (h : y ≠ 1) : x < y ↔ x ≤ parent y := sorry

instance : OrderBot N where
  bot := 1
  bot_le x := sorry

instance : PredOrder N where
  pred := parent
  pred_le := parent_le
  min_of_le_pred hap := sorry
  le_pred_of_lt {a} {b} hab := (lt_iff_le_parent hab.ne_bot).mp hab

def R' (a:SM) : N ≃ N := {
  toFun := fun x ↦ (e a) * x
  invFun := fun x ↦ (e a)⁻¹ * x
  left_inv := sorry
  right_inv := sorry
}

@[simp]
lemma R'_axiom_iia' {a b : SM} {y:N} : R' a y = R' b y ↔ a = b := sorry

abbrev M := SM ⊕ N

variable (f g h : ℕ → ℕ)

instance rel : Setoid N := {
  r := fun x y => ∃ n : ℤ, y = (e 0)^n * x
  iseqv := sorry
}

/-- `fill D` is the set of elements of the form (e 0)^n x with x in D and n an integer. -/
def fill (D: Finset N) : Set N := { y | ∃ x, x ≈ y ∧ x ∈ D }

abbrev generators (A : Finset SM) : Finset ℕ := A.biUnion DFinsupp.support ∪ {0}

lemma generators_nonempty (A : Finset SM): (generators A).Nonempty := sorry

abbrev fresh (A: Finset SM) (n:ℕ) : ℕ := ((generators A).max' (generators_nonempty A)) + (n + 1)

/-- The basis elements of an element `x` of the free group `N` are the set of indices `a` of the generators `e a` appearing in the minimal word of `x`, together with `0`. -/
abbrev basis_elements (x:N) : Finset SM := Finset.image (fun (a, _) ↦ a) x.toWord.toFinset ∪ {0}

abbrev basis_elements' (x:M) : Finset SM := match x with
  | Sum.inl a => {a}
  | Sum.inr x => basis_elements x

end Eq1729
