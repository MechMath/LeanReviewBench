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

namespace Eq1722

namespace Greedy

noncomputable section

open AdjoinFresh PartialMagma

structure Laws {α : Type} (E : PreExtension α) : Prop where
  eq1722 {x y xy xyy} : xy ∈ E x y → xyy ∈ E xy y → ∃yy, yy ∈ E y y ∧ x ∈ E yy xyy
  law2 {x y z xy zy} : xy ∈ E x y → zy ∈ E z y → xy = zy → x = z
  law3 {x xx} : xx ∈ E x x → ∃ xxx, ∃ xxxx, xxx ∈ E xx x ∧ xxxx ∈ E xxx x
  law4 {x z zx} : zx ∈ E z x → zx = x → ∃ xx, xx ∈ E x x

def Laws_equiv {α β : Type} (e : α ≃ β) (E : PreExtension β) (ok : Laws E) :
  Laws (Equiv.movePreExtension e E) where
  eq1722 xy_mem xyy_mem := sorry
  law2 xy_mem zy_mem eq := sorry
  law3 xx_mem := sorry
  law4 zx_mem eq := sorry

scoped instance : ExtensionRules where
  laws := Laws
  laws_equiv := Laws_equiv

class Extension1 extends ExtensionBase where
  b_eq_a : b = a

namespace Extension1

variable [Extension1]

inductive F
  | ai : Fin 4 → F -- indexed shifted by 1
  | b₀ : F
  | bi : Fin 4 → F -- same
  deriving DecidableEq, Fintype

open F

open ExtensionBase

@[scoped aesop unsafe 50% [constructors]]
inductive Next : ℕ ⊕ F → ℕ ⊕ F → ℕ ⊕ F → Prop
  | base {x y z} : z ∈ x ◯ y → Next (.inl x) (.inl y) (.inl z)
  | new : Next (.inl a) (.inl a) (.inr $ ai 0)
  | sq_0 : Next (.inr $ ai 0) (.inr $ ai 0) (.inr $ ai 1)
  | sq_1 : Next (.inr $ ai 1) (.inr $ ai 1) (.inr $ ai 2)
  | sq_2 : Next (.inr $ ai 2) (.inr $ ai 2) (.inr $ ai 3)
  | sq_3 : Next (.inr $ ai 3) (.inr $ ai 3) (.inr $ ai 0)
  | extra1_base : Next (.inr $ ai 0) (.inl a) (.inr b₀)
  | extra1_0 : Next (.inr $ ai 1) (.inr $ ai 0) (.inr $ bi 0)
  | extra1_1 : Next (.inr $ ai 2) (.inr $ ai 1) (.inr $ bi 1)
  | extra1_2 : Next (.inr $ ai 3) (.inr $ ai 2) (.inr $ bi 2)
  | extra1_3 : Next (.inr $ ai 0) (.inr $ ai 3) (.inr $ bi 3)
  | extra2_base : Next (.inr b₀) (.inl a) (.inr $ ai 1)
  | extra2_0 : Next (.inr $ bi 0) (.inr $ ai 0) (.inr $ ai 2)
  | extra2_1 : Next (.inr $ bi 1) (.inr $ ai 1) (.inr $ ai 3)
  | extra2_2 : Next (.inr $ bi 2) (.inr $ ai 2) (.inr $ ai 0)
  | extra2_3 : Next (.inr $ bi 3) (.inr $ ai 3) (.inr $ ai 1)
  | extra3_0 : Next (.inr $ ai 2) (.inr $ ai 0) (.inr $ ai 0)
  | extra3_1 : Next (.inr $ ai 3) (.inr $ ai 1) (.inr $ ai 1)
  | extra3_2 : Next (.inr $ ai 0) (.inr $ ai 2) (.inr $ ai 2)
  | extra3_3 : Next (.inr $ ai 1) (.inr $ ai 3) (.inr $ ai 3)
  | extra4_0 : Next (.inr $ ai 0) (.inr $ ai 1) (.inr $ ai 0)
  | extra4_1 : Next (.inr $ ai 1) (.inr $ ai 2) (.inr $ ai 1)
  | extra4_2 : Next (.inr $ ai 2) (.inr $ ai 3) (.inr $ ai 2)
  | extra4_3 : Next (.inr $ ai 3) (.inr $ ai 0) (.inr $ ai 3)
  | extra5_base : Next (.inr $ ai 0) (.inr b₀) (.inl a)
  | extra5_0 : Next (.inr $ ai 1) (.inr $ bi 0) (.inr $ ai 0)
  | extra5_1 : Next (.inr $ ai 2) (.inr $ bi 1) (.inr $ ai 1)
  | extra5_2 : Next (.inr $ ai 3) (.inr $ bi 2) (.inr $ ai 2)
  | extra5_3 : Next (.inr $ ai 0) (.inr $ bi 3) (.inr $ ai 3)

abbrev next : PreExtension (ℕ ⊕ F) := fun a b => {c | Next a b c}

end Extension1

class Extension2 extends ExtensionBase where
   a_ne_b : a ≠ b
   bb : ℕ
   bb_mem : bb ∈ E b b

namespace Extension2

variable [Extension2]

open ExtensionBase

attribute [scoped aesop safe destruct] a_ne_b

inductive Relevant : ℕ → Prop
  | mk {d} : a ∈ d ◯ b → Relevant d

inductive Next : ℕ ⊕ Unit → ℕ ⊕ Unit → ℕ ⊕ Unit → Prop
  | base {x y z} : z ∈ x ◯ y → Next (.inl x) (.inl y) (.inl z)
  | new : Next (.inl a) (.inl b) (.inr ())
  | extra {d} : Relevant d → Next (.inl bb) (.inr ()) (.inl d)

abbrev next : PreExtension (ℕ ⊕ Unit) := fun a b => {c | Next a b c}

end Extension2

open ExtensionBase

theorem lift : ∀ (E : Extension ℕ) (a b : ℕ),
  ∃ E' : Extension ℕ, E ≤ E' ∧ E' ∈ {e : Extension ℕ | (e.1 a b).Nonempty} := sorry

variable (e₀ : Extension ℕ)

include e₀ in
theorem exists_extension :
    ∃ op : ℕ → ℕ → ℕ,
    (∀ x y, x = op (op y y) (op (op x y) y)) ∧
    (∀ {x y z}, z ∈ e₀.1 x y → z = op x y) := sorry

def GreedyMagma (_ : Extension ℕ) := ℕ

instance (n) : OfNat (GreedyMagma e₀) n := inferInstanceAs (OfNat Nat n)

noncomputable instance instMagma : Magma (GreedyMagma e₀) where
  op := (exists_extension e₀).choose

theorem _root_.PartialMagma.Extension.eq1722 : Equation1722 (GreedyMagma e₀) := sorry

theorem Extension.base : ∀ {x y z : GreedyMagma e₀}, z ∈ e₀.1 x y → z = x ◇ y := sorry

end

end Greedy

open Greedy PartialMagma

end Eq1722
