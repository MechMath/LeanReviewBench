import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Order
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Defs
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Sum.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Order.Preorder.Chain
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Tactic.FinCases
import dep.equational_theories.AdjoinFresh
import dep.equational_theories.EquationLawConversion
import dep.equational_theories.Equations.Command
import dep.equational_theories.Equations.Eqns3000_3999
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

namespace Refutation_3308

namespace Greedy

noncomputable section

open AdjoinFresh PartialMagma ExtensionBase

abbrev Fresh := Fin 10

structure Laws {α : Type} (E : PreExtension α) : Prop where
  eq3308 {x y xy yx} : xy ∈ E x y → yx ∈ E y x → ∃ xyx ∈ E x yx, xy ∈ E x xyx
  not_left {x y z} : z ∈ E x y → x ≠ z
  not_right {x y z} : z ∈ E x y → y ≠ z
  right_cancel {x x' y xy} : xy ∈ E x y → xy ∈ E x' y → x = x'
  law3 {x y xy yxy} : xy ∈ E x y → yxy ∈ E y xy → ∃ yx, yx ∈ E y x
  law3' {x y xy xyy} : xy ∈ E x y → xyy ∈ E xy y → ∃ yx, yx ∈ E y x
  law5 {x y w z} : z ∈ E x y → y ∈ E w z → y ≠ z → ∃ yx, yx ∈ E y x

def Laws_equiv {α β : Type} (e : α ≃ β) (E : PreExtension β) (ok : Laws E) :
  Laws (Equiv.movePreExtension e E) where
  eq3308 xy_mem yx_mem := sorry
  not_left xy_mem h := ok.not_left xy_mem (sorry)
  not_right xy_mem h := ok.not_right xy_mem (sorry)
  right_cancel xy_mem xy_mem' := sorry
  law3 xy_mem yxy_mem := sorry
  law3' xy_mem xyy_mem := sorry
  law5 xy_mem wz_mem ineq := sorry

scoped instance : ExtensionRules where
  laws := Laws
  laws_equiv := Laws_equiv

attribute [scoped aesop safe forward] not_def

attribute [scoped aesop safe forward] PreExtension.OK.func

attribute [scoped aesop safe forward] Laws.eq3308

attribute [scoped aesop safe destruct] Laws.not_right

attribute [scoped aesop safe destruct] Laws.not_left

class Extension1 extends ExtensionBase where
  b_eq_a : b = a

namespace Extension1

variable [Extension1]

open ExtensionBase

@[scoped aesop unsafe 50% [constructors]]
inductive Next : ℕ ⊕ Fresh → ℕ ⊕ Fresh → ℕ ⊕ Fresh → Prop
  | base {x y z} : z ∈ x ◯ y → Next (.inl x) (.inl y) (.inl z)
  | new : Next (.inl a) (.inl a) (.inr 0)
  | extra0 : Next (.inl a) (.inr 0) (.inr 1)
  | extra1 : Next (.inl a) (.inr 1) (.inr 0)
  | extra2 : Next (.inr 0) (.inl a) (.inr 2)
  | extra3 : Next (.inl a) (.inr 2) (.inr 3)
  | extra4 : Next (.inl a) (.inr 3) (.inr 1)
  | extra5 : Next (.inr 0) (.inr 1) (.inr 4)
  | extra6 : Next (.inr 0) (.inr 4) (.inr 2)
  | extra7 : Next (.inr 1) (.inl a) (.inr 5)
  | extra8 : Next (.inl a) (.inr 5) (.inr 6)
  | extra9 : Next (.inl a) (.inr 6) (.inr 0)
  | extra10 : Next (.inr 1) (.inr 0) (.inr 7)
  | extra11 : Next (.inr 1) (.inr 7) (.inr 5)
  | extra12 : Next (.inr 1) (.inr 4) (.inr 8)
  | extra13 : Next (.inr 1) (.inr 8) (.inr 7)
  | extra14 : Next (.inr 0) (.inr 7) (.inr 9)
  | extra15 : Next (.inr 0) (.inr 9) (.inr 4)

abbrev next : PreExtension (ℕ ⊕ Fresh) := fun a b => {c | Next a b c}

end Extension1

class Extension2 extends ExtensionBase where
  a_ne_b : a ≠ b
  d : ℕ
  ba_def : d ∈ E b a

namespace Extension2

variable [Extension2]

open ExtensionBase PartialMagma

open ExtensionBase

@[scoped aesop unsafe 50% [constructors]]
inductive Next : ℕ ⊕ Fresh → ℕ ⊕ Fresh → ℕ ⊕ Fresh → Prop
  | base {x y z} : z ∈ x ◯ y → Next (.inl x) (.inl y) (.inl z)
  | new :  Next (.inl a) (.inl b) (.inr 0)
  | extra0 : Next (.inl b) (.inr 0) (.inr 1)
  | extra1 : Next (.inl b) (.inr 1) (.inl d)
  | extra2 : Next (.inl a) (.inl d) (.inr 2)
  | extra3 : Next (.inl a) (.inr 2) (.inr 0)

abbrev next : PreExtension (ℕ ⊕ Fresh) := fun a b => {c | Next a b c}

end Extension2

class Extension3 extends ExtensionBase where
  a_ne_b : a ≠ b
  ba_not_def {d} : d ∉ E b a
  a_not_im_b {d} : a ∉ E d b
  b_not_im_a {d} : b ∉ E d a

namespace Extension3

variable [Extension3]

open ExtensionBase

attribute [scoped aesop safe destruct] ba_not_def

attribute [scoped aesop safe destruct] a_not_im_b

attribute [scoped aesop safe destruct] b_not_im_a

@[scoped aesop unsafe 50% [constructors]]
inductive Next : ℕ ⊕ Fresh → ℕ ⊕ Fresh → ℕ ⊕ Fresh → Prop
  | base {x y z} : z ∈ x ◯ y → Next (.inl x) (.inl y) (.inl z)
  | new :  Next (.inl a) (.inl b) (.inr 0)
  | extra0 : Next (.inl b) (.inr 0) (.inr 1)
  | extra1 : Next (.inl b) (.inr 1) (.inr 2)
  | extra2 : Next (.inl b) (.inl a) (.inr 2)
  | extra3 : Next (.inl a) (.inr 2) (.inr 3)
  | extra4 : Next (.inl a) (.inr 3) (.inr 0)

abbrev next : PreExtension (ℕ ⊕ Fresh) := fun a b => {c | Next a b c}

end Extension3

open ExtensionBase

theorem lift : ∀ (E : Extension ℕ) (a b : ℕ),
  ∃ E' : Extension ℕ, E ≤ E' ∧ E' ∈ {e : Extension ℕ | (e.1 a b).Nonempty} := sorry

variable (e₀ : Extension ℕ)

include e₀ in
theorem exists_extension :
    ∃ op : ℕ → ℕ → ℕ,
    (∀ x y, op x y= op x (op x (op y x))) ∧
    (∀ {x y z}, z ∈ e₀.1 x y → z = op x y) := sorry

def GreedyMagma (_ : Extension ℕ) := ℕ

instance (n) : OfNat (GreedyMagma e₀) n := inferInstanceAs (OfNat Nat n)

noncomputable instance instMagma : Magma (GreedyMagma e₀) where
  op := (exists_extension e₀).choose

theorem _root_.PartialMagma.Extension.eq3308 : Equation3308 (GreedyMagma e₀) := sorry

theorem Extension.base : ∀ {x y z : GreedyMagma e₀}, z ∈ e₀.1 x y → z = x ◇ y := sorry

end

end Greedy

open Greedy PartialMagma
