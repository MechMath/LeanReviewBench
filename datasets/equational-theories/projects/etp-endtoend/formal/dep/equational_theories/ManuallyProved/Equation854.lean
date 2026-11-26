import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finset.Order
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Defs
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Logic.Equiv.Basic
import Mathlib.Order.Preorder.Chain
import dep.equational_theories.Completeness
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
import dep.equational_theories.MemoFinOp
import dep.equational_theories.ParseImplications
import dep.equational_theories.Preorder

set_option backward.isDefEq.respectTransparency false

set_option backward.whnf.reducibleClassField false

namespace Refutation_854

def G := FreeMagmaWithLaws ℕ {Law854}

instance : Magma G := inferInstanceAs (Magma (FreeMagmaWithLaws ..))

theorem law : ∀ (x y z : G), x = x ◇ ((y ◇ z) ◇ (x ◇ z)) := sorry

def Rel (x y : G) := ∃ z, y = z ◇ x

local infix:50 " ⇝ " => Rel

prefix:max "↟" => embed (singleton Law854)

namespace Greedy

noncomputable section

variable (G) in
abbrev PreExtension := ℕ → ℕ → Set ℕ

structure PreExtension.OK (E : PreExtension) : Prop where
  finite : Set.Finite {x : (ℕ × ℕ) × ℕ | x.2 ∈ E x.1.1 x.1.2}
  func {x y} : Set.Subsingleton (E x y)
  eq854 {x y z xz yz yzxz} : xz ∈ E x z → yz ∈ E y z → yzxz ∈ E yz xz → x ∈ E x yzxz
  eq8 {x xx} : xx ∈ E x x → x ∈ E x xx
  eq101 {x y xy xyx} : xy ∈ E x y → xyx ∈ E xy x → x ∈ E x xyx
  eq46155 {x y xy xxy} : xy ∈ E x y → xxy ∈ E x xy → xy ∈ E xy xxy
  eq378 {x y xy} : xy ∈ E x y → xy ∈ E xy y
  no_idem {x} : x ∉ E x x
  aux {x y xy} : xy ∈ E x y → x ∈ E x xy → x = y
  uniq_fac {x y x' y' xy} : xy ∈ E x y → xy ∈ E x' y' → xy = x ∨ xy = x' ∨ (x, y) = (x', y')
  mono {x y xy} : xy ∈ E x y → xy = x ∨ x < xy ∧ y < xy

variable (G) in
abbrev Extension := {E : PreExtension // E.OK}

class Extension1 where
  E : PreExtension
  ok : E.OK
  a : ℕ
  b : ℕ
  not_def {c} : c ∉ E a b

namespace Extension1

variable [Extension1]

local infix:80 " ◯ " => E

def dom : Finset Nat :=
  insert a <| insert b <| ok.finite.toFinset.biUnion fun ((a, b), c) => {a, b, c}

theorem dom_r {a b c} (h : c ∈ a ◯ b) : b ∈ dom := sorry

def c : Nat := dom.sup id + 1

local notation x:51 " ≫ " y:51 => y ∈ y ◯ x

inductive Relevant : ℕ → Prop
  | mk {b1 b2} : b ∈ b1 ◯ b2 → b1 ≠ b → b2 ≫ a → Relevant b1

inductive Target (p : Prop) : ℕ → Prop
  | protected b : Target p b
  | rel {b1} : p → Relevant b1 → Target p b1

theorem Target.dom {p x} : Target p x → x ∈ dom
  := sorry

@[mk_iff]
inductive Extra : ℕ → ℕ → Prop
  | left {b1} : Target (b ≫ b1) b1 → Extra c b1
  | right {x} : Target True x → Extra x c

inductive Next : ℕ → ℕ → ℕ → Prop
  | base {x y z} : z ∈ x ◯ y → Next x y z
  | new : Next a b c
  | extra {x y} : Extra x y → Next x y x

abbrev next : PreExtension := fun a b => {c | Next a b c}

theorem Next.eq8 {x xx : ℕ} (h : Next x x xx) : Next x xx x := sorry

theorem Next.no_idem {x} : ¬Next x x x := sorry

end Extension1

variable (e₀ : Extension)

include e₀ in
theorem exists_extension :
    ∃ op : ℕ → ℕ → ℕ,
    (∀ x y z, x = op x (op (op y z) (op x z))) ∧
    (∀ {x y}, op x (op x y) = x → x = y) ∧
    (∀ {x y z}, z ∈ e₀.1 x y → z = op x y) := sorry

def GreedyMagma (_ : Extension) := ℕ

instance (n) : OfNat (GreedyMagma e₀) n := inferInstanceAs (OfNat Nat n)

noncomputable instance instMagma : Magma (GreedyMagma e₀) where
  op := (exists_extension e₀).choose

theorem Extension.eq854 : Equation854 (GreedyMagma e₀) := sorry

theorem Extension.aux : ∀ {x y : GreedyMagma e₀}, x ◇ (x ◇ y) = x → x = y := sorry

theorem Extension.base : ∀ {x y z : GreedyMagma e₀}, z ∈ e₀.1 x y → z = x ◇ y := sorry

private def lexLt : Nat × Nat → Nat × Nat → Prop :=
  fun a b => a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

private instance : DecidableRel lexLt := fun _ _ => instDecidableOr

private instance lexLt_isTrans :
    IsTrans ((ℕ × ℕ) × ℕ) (fun a b : (ℕ × ℕ) × ℕ => lexLt a.1 b.1) := sorry

end

end Greedy

open Greedy
