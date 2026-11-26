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
import Mathlib.Tactic.CasesM
import Mathlib.Tactic.NthRewrite
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
import dep.equational_theories.Preorder

namespace FreeMagma

variable {α : Type}

def Everywhere (P : FreeMagma α → Prop) : FreeMagma α → Prop
  | .Leaf x => P (.Leaf x)
  | x ⋆ y => x.Everywhere P ∧ y.Everywhere P ∧ P (x ⋆ y)

theorem Everywhere.left {P : FreeMagma α → Prop} {x y : FreeMagma α} (h: Everywhere P (x ⋆ y)): Everywhere P x := sorry

theorem Everywhere.right {P : FreeMagma α → Prop} {x y : FreeMagma α} (h: Everywhere P (x ⋆ y)): Everywhere P y := sorry

def SubtermOf (x : FreeMagma α) : (y : FreeMagma α) → Prop
| .Leaf a => x = .Leaf a
| a ⋆ b => x = a ⋆ b ∨ SubtermOf x a ∨ SubtermOf x b

@[refl]
theorem SubtermOf.refl (x : FreeMagma α) : SubtermOf x x := sorry

lemma SubtermOf.left {x a b: FreeMagma α} (h : SubtermOf x a) : SubtermOf x (a ⋆ b) := sorry

lemma SubtermOf.right {x a b: FreeMagma α} (h : SubtermOf x b) : SubtermOf x (a ⋆ b) := sorry

variable (rw : FreeMagma α → FreeMagma α)

class IsProj : Prop where
  proj : ∀ x, SubtermOf (rw x) x

variable [hproj: IsProj rw]

end FreeMagma

namespace Confluence

open FreeMagma

variable {α : Type}

variable (rw : FreeMagma α → FreeMagma α)

def bu : FreeMagma α → FreeMagma α
  | .Leaf x => rw x
  | x ⋆ y => rw (bu x ⋆ bu y)

attribute [simp] bu.eq_1

abbrev buFixed x := bu rw x = x

def NF (x : FreeMagma α) : Prop := x.Everywhere (fun y => rw y = y)

class IsProjOrNF : Prop where
  proj_or_nf : ∀ x, SubtermOf (rw x) x ∨ NF rw (rw x)

instance [hproj: IsProj rw]: IsProjOrNF rw := sorry

variable [hproj: IsProjOrNF rw]

@[simp] theorem bu_idem x : buFixed rw (bu rw x) := sorry

@[simp] theorem buFixed_rw_op {x} {y}
    (hx: bu rw x = x) (hy: bu rw y = y): buFixed rw (rw (x ⋆ y)) := sorry

@[reducible] def ConfMagma := {x : FreeMagma α // bu rw x = x }

instance : Coe α (ConfMagma rw) where
  coe x := ⟨bu rw x, bu_idem rw x⟩

instance : Magma (ConfMagma rw) where
  op := fun x y ↦ ⟨bu rw (x.1 ◇ y.1), bu_idem rw _⟩

instance [DecidableEq α] : DecidableEq (ConfMagma rw) :=
  inferInstanceAs (DecidableEq {x : FreeMagma α // buFixed rw x })

/-- Refutation tactic for dedicable FreeMagma equations -/
macro "refute" : tactic =>
  `(tactic |(
    show (¬ ∀ _,_)
    push Not
    first
    | (use (0 : Nat); simp only [ne_eq, Subtype.mk.injEq]; decide +kernel)
    | (use (0 : Nat), (1 : Nat); simp only [ne_eq, Subtype.mk.injEq]; decide +kernel)
    | (use (0 : Nat), (1 : Nat), (2: Nat); simp only [ne_eq, Subtype.mk.injEq]; decide +kernel)
    | (use (0 : Nat), (1 : Nat), (2: Nat), (3: Nat); simp only [ne_eq, Subtype.mk.injEq]; decide +kernel)
    | (use (0 : Nat), (1 : Nat), (2: Nat), (3: Nat), (4: Nat); simp only [ne_eq, Subtype.mk.injEq]; decide +kernel)
    | (use (0 : Nat), (1 : Nat), (2: Nat), (3: Nat), (4: Nat), (5: Nat); simp only [ne_eq, Subtype.mk.injEq]; decide +kernel)
    ))

register_simp_attr confluence_simps

scoped syntax "subterm" : tactic

scoped macro_rules
| `(tactic| subterm) => `(tactic|
  first
  | apply FreeMagma.SubtermOf.refl
  | apply FreeMagma.SubtermOf.left
    subterm
  | apply FreeMagma.SubtermOf.right
    subterm
)

scoped syntax "everywhere" " at " ident : tactic

scoped macro_rules
| `(tactic| everywhere at $h:ident) => `(tactic|
  first
  | assumption
  | apply FreeMagma.Everywhere.left at $h
    everywhere at $h
  | apply FreeMagma.Everywhere.right at $h
    everywhere at $h
)

scoped syntax "bufixed" : tactic

scoped macro_rules
| `(tactic| bufixed) => `(tactic|
  first
  | assumption
  | apply Confluence.buFixed_rw_op
    all_goals bufixed
)

end Confluence
