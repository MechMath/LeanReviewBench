import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Data.Countable.Defs
import Mathlib.Data.FinEnum
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Order
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.AList
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Defs
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Functor
import Mathlib.Data.Sum.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Order.Preorder.Chain
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Tactic.DeriveFintype
import dep.equational_theories.AdjoinFresh
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
import dep.equational_theories.ParseImplications
import dep.equational_theories.PartialMagma
import dep.equational_theories.Preorder

set_option backward.isDefEq.respectTransparency false

set_option backward.whnf.reducibleClassField false

namespace Eq1076

namespace Greedy

noncomputable section

open AdjoinFresh PartialMagma

structure Laws {α : Type} (E : PreExtension α) : Prop where
  eq1076 {x y xy xxy} : xy ∈ E x y → xxy ∈ E x xy → ∃xxyy, xxyy ∈ E xxy y ∧ x ∈ E y xxyy
  not_idempotent {x} : x ∉ E x x

def Laws_equiv {α β : Type} (e : α ≃ β) (E : PreExtension β) (ok : Laws E) :
  Laws (Equiv.movePreExtension e E) where
  eq1076 xy_mem xxy_mem := sorry
  not_idempotent h := sorry

scoped instance : ExtensionRules where
  laws := Laws
  laws_equiv := Laws_equiv

class Extension1 extends ExtensionBase where

namespace Extension1

variable [Extension1]

open ExtensionBase

/-- We use `F := Unit ⊕ Fin dom_bound ⊕ Fin dom_bound` for our fresh variables.
The unit corresponds to c, the first Fin to c'ᵢ, the second one to c''ᵢ.
To easily infer FinEnum we keep it as is, might also be possible to define an inductive type instead -/
private abbrev F := Unit ⊕ Fin dom_bound ⊕ Fin dom_bound

open ExtensionBase

@[scoped aesop unsafe 50% [constructors]]
inductive Next : ℕ ⊕ F → ℕ ⊕ F → ℕ ⊕ F → Prop
  | base {x y z} : z ∈ x ◯ y → Next (.inl x) (.inl y) (.inl z)
  | new : Next (.inl a) (.inl b) (.inr $ .inl ())
  | extra1 {d} (h : b ∈ a ◯ d) :
    Next (.inr $ .inl ()) (.inl d) (.inr $ .inr $ .inl ⟨d, lt_dom_bound $ dom_r h⟩)
  | extra2 {d} (h : b ∈ a ◯ d) :
    Next (.inl d) (.inr $ .inr $ .inl ⟨d, lt_dom_bound $ dom_r h⟩) (.inl a)
  | extra3_1 {d e} (h : b ∈ a ◯ d) : d ≠ e → e ∈ d ◯ a →
    Next (.inr $ .inr $ .inl ⟨d, lt_dom_bound $ dom_r h⟩)
      (.inr $ .inr $ .inr ⟨d, lt_dom_bound $ dom_r h⟩) (.inl d)
  | extra3_2 {d e} (h : b ∈ a ◯ d) : d ≠ e → e ∈ d ◯ a →
    Next (.inl e) (.inr $ .inr $ .inl ⟨d, lt_dom_bound $ dom_r h⟩)
      (.inr $ .inr $ .inr ⟨d, lt_dom_bound $ dom_r h⟩)
  | extra4_1 {d} (h : b ∈ a ◯ d) : d ∈ d ◯ a →
    Next (.inr $ .inr $ .inl ⟨d, lt_dom_bound $ dom_r h⟩) (.inl a) (.inl d)
  | extra4_2 {d} (h : b ∈ a ◯ d) : d ∈ d ◯ a →
    Next (.inl d) (.inr $ .inr $ .inl ⟨d, lt_dom_bound $ dom_r h⟩) (.inl a)

abbrev next : PreExtension (ℕ ⊕ F) := fun a b => {c | Next a b c}

end Extension1

open ExtensionBase

theorem lift : ∀ (E : Extension ℕ) (a b : ℕ),
  ∃ E' : Extension ℕ, E ≤ E' ∧ E' ∈ {e : Extension ℕ | (e.1 a b).Nonempty} := sorry

variable (e₀ : Extension ℕ)

include e₀ in
theorem exists_extension :
    ∃ op : ℕ → ℕ → ℕ,
    (∀ x y, x = op y (op (op x (op x y)) y)) ∧
    (∀ {x y z}, z ∈ e₀.1 x y → z = op x y) := sorry

def GreedyMagma (_ : Extension ℕ) := ℕ

instance (n) : OfNat (GreedyMagma e₀) n := inferInstanceAs (OfNat Nat n)

noncomputable instance instMagma : Magma (GreedyMagma e₀) where
  op := (exists_extension e₀).choose

theorem _root_.PartialMagma.Extension.eq1076 : Equation1076 (GreedyMagma e₀) := sorry

theorem Extension.base : ∀ {x y z : GreedyMagma e₀}, z ∈ e₀.1 x y → z = x ◇ y := sorry

end

end Greedy

open Greedy PartialMagma

end Eq1076
