import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.Data.Finset.Order
import Mathlib.Data.Finset.Union
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.AList
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Defs
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Functor
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.Logic.Equiv.Basic
import Mathlib.Order.Preorder.Chain
import Mathlib.Tactic.Group
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
import dep.equational_theories.FreshGenerator
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw
import dep.equational_theories.ParseImplications
import dep.equational_theories.Preorder

set_option backward.isDefEq.respectTransparency false

set_option backward.whnf.reducibleClassField false

namespace Eq917

private abbrev A := FreeGroup Nat

namespace Greedy

noncomputable section

open FreshGenerator

private abbrev x₁ := FreeGroup.of 1

private abbrev x₂ := FreeGroup.of 2

abbrev PreExtension := A → Set A

structure PreExtension.OK (E : PreExtension) : Prop where
  finite : Set.Finite {x : A × A | x.2 ∈ E x.1}
  func {a} : Set.Subsingleton (E a)
  base : x₁ ∈ E 1
  eq917 {a b c} : b ∈ E a → c ∈ E (b * a⁻¹ * x₁⁻¹) → a⁻¹ ∈ E (c * x₁)
  aux {a b c d} : b ∈ E a → d ∈ E c → b * a⁻¹ = d * c⁻¹ → a = c -- b = d follows from func
  aux' {a b} : b ∈ E a → b * a⁻¹ ≠ x₁⁻¹

abbrev Extension := {E : PreExtension // E.OK}

class Extension1 where
  E : PreExtension
  ok : E.OK
  d : A
  not_def {c} : c ∉ E d

namespace Extension1

variable [Extension1]

def old : Finset A :=
  insert d <| ok.finite.toFinset.biUnion fun (a, b) => {a, b}

def c := freshGenerator old

attribute [local aesop norm simp] forgetOld_old

attribute [local aesop norm simp] MonoidHom.map_mul

inductive Relevant : A → Prop
  | mk {a b} : b ∈ E a → d = b * a⁻¹ * x₁⁻¹ → Relevant a

@[mk_iff]
inductive Next : A → A → Prop
  | base {a b} : b ∈ E a → Next a b
  | new {a b} : a = d → b = c → Next a b
  | extra {a e f} : Relevant a → e = c * x₁ → f = a⁻¹ →  Next e f

abbrev next : PreExtension := fun a => {b | Next a b}

end Extension1

variable (e₀ : Extension)

include e₀ in
theorem exists_extension :
    ∃ op : A → A,
    (∀ x, op (op ((op x * x⁻¹)*(op 1)⁻¹)*op 1) = x⁻¹) ∧
    (∀ {x y}, y ∈ e₀.1 x → y = op x) := sorry

def GreedyMagma (_ : Extension) := A

def f (e₀ : Extension) : A → A := (exists_extension e₀).choose

def op (e₀ : Extension) (x y : A) : A := f e₀ (y*x⁻¹) * x

noncomputable instance instMagma : Magma (GreedyMagma e₀) where
  op x y:= op e₀ x y

theorem eq917 : Equation917 (GreedyMagma e₀) := sorry

end

end Greedy

open Greedy

end Eq917
