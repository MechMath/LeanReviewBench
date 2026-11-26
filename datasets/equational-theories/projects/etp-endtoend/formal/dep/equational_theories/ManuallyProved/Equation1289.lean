import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Data.Countable.Defs
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

namespace Eq1289

namespace Greedy

noncomputable section

open AdjoinFresh PartialMagma

structure Laws {α : Type} (E : PreExtension α) : Prop where
  eq1289 {x y xy xyy xyyy} : xy ∈ E x y → xyy ∈ E xy y → xyyy ∈ E xyy y → x ∈ E y xyyy
  right_cancel {x y z xy zy} : xy ∈ E x y → zy ∈ E z y → xy = zy → x = z
  idem_l {x y xy} : xy ∈ E x y → x ∈ E x x
  idem_r {x y xy} : xy ∈ E x y → y ∈ E y y
  idem_o {x y xy} : xy ∈ E x y → xy ∈ E xy xy

def Laws_equiv {α β : Type} (e : α ≃ β) (E : PreExtension β) (ok : Laws E) :
  Laws (Equiv.movePreExtension e E) where
  eq1289 xy_mem xyy_mem xyyy_mem := sorry
  right_cancel xy_mem zy_mem := sorry
  idem_l xy_mem := sorry
  idem_r xy_mem := sorry
  idem_o xy_mem := sorry

scoped instance : ExtensionRules where
  laws := Laws
  laws_equiv := Laws_equiv

class Extension1 extends ExtensionBase where
  b_eq_a : b = a
  not_im_l {y z}: z ∉ E a y
  not_im_r {x z}: z ∉ E x a
  not_im_o {x y}: a ∉ E x y

namespace Extension1

variable [Extension1]

attribute [scoped aesop safe destruct] not_im_l

attribute [scoped aesop safe destruct] not_im_r

attribute [scoped aesop safe destruct] not_im_o

abbrev F := Empty

open ExtensionBase

@[scoped aesop unsafe 50% [constructors]]
inductive Next : ℕ ⊕ F → ℕ ⊕ F → ℕ ⊕ F → Prop
  | base {x y z} : z ∈ x ◯ y → Next (.inl x) (.inl y) (.inl z)
  | new : Next (.inl a) (.inl a) (.inl a)

abbrev next : PreExtension (ℕ ⊕ F) := fun a b => {c | Next a b c}

end Extension1

class Extension2 extends ExtensionBase where
   a_ne_b : a ≠ b
   a_idem : a ∈ E a a
   b_idem : b ∈ E b b

namespace Extension2

variable [Extension2]

open ExtensionBase

attribute [scoped aesop safe destruct] a_ne_b

attribute [scoped aesop safe forward] a_idem

attribute [scoped aesop safe forward] b_idem

inductive Relevant : ℕ → Prop
  | mk {d e} : e ∈ d ◯ b  → a ∈ e ◯ b → Relevant d

theorem Relevant.idem {d} : Relevant d → d ∈ d ◯ d
  := sorry

abbrev F := Unit

@[scoped aesop unsafe 50% [constructors]]
inductive Next : ℕ ⊕ F → ℕ ⊕ F → ℕ ⊕ F → Prop
  | base {x y z} : z ∈ x ◯ y → Next (.inl x) (.inl y) (.inl z)
  | new : Next (.inl a) (.inl b) (.inr ())
  | idem : Next (.inr ()) (.inr ()) (.inr ())
  | extra {d} : Relevant d → Next (.inl b) (.inr ()) (.inl d)

abbrev next : PreExtension (ℕ ⊕ F) := fun a b => {c | Next a b c}

end Extension2

open ExtensionBase

theorem lift : ∀ (E : Extension ℕ) (a b : ℕ),
  ∃ E' : Extension ℕ, E ≤ E' ∧ E' ∈ {e : Extension ℕ | (e.1 a b).Nonempty} := sorry

variable (e₀ : Extension ℕ)

include e₀ in
theorem exists_extension :
    ∃ op : ℕ → ℕ → ℕ,
    (∀ x y, x = op y (op (op (op x y) y) y)) ∧
    (∀ {x y z}, z ∈ e₀.1 x y → z = op x y) := sorry

def GreedyMagma (_ : Extension ℕ) := ℕ

instance (n) : OfNat (GreedyMagma e₀) n := inferInstanceAs (OfNat Nat n)

noncomputable instance instMagma : Magma (GreedyMagma e₀) where
  op := (exists_extension e₀).choose

theorem _root_.PartialMagma.Extension.eq1289 : Equation1289 (GreedyMagma e₀) := sorry

theorem Extension.base : ∀ {x y z : GreedyMagma e₀}, z ∈ e₀.1 x y → z = x ◇ y := sorry

end

end Greedy

open Greedy PartialMagma

end Eq1289
