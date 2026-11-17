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
import dep.equational_theories.Confluence
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

open FreeMagma Confluence

variable {α: Type} [DecidableEq α]

local macro "prove" rule:ident : tactic => `(tactic| (
  unfold $rule
  split
  · injections
    subst_eqs
    split
    · exfalso
      casesm* _ ∧ _
      subst_eqs
    · rfl
  · rfl
))

local macro "prove_proj" rule:ident : tactic => `(tactic| (
  intro x
  unfold $rule
  repeat' split
  any_goals subterm
))

namespace rw477

def rule : FreeMagma α → FreeMagma α
  | m@(y₁ ⋆ (x ⋆ (y₂ ⋆ (y₃ ⋆ y₄)))) =>
      if y₁ = y₂ ∧ y₁ = y₃ ∧ y₁ = y₄ then
        x
      else
        m
  | m => m

instance rule_projection : IsProj (@rule α _) := sorry

end rw477

namespace rw467

def rule : FreeMagma α → FreeMagma α
  | m@(y₁ ⋆ (x ⋆ (x₂ ⋆ (y₂ ⋆ y₃)))) =>
      if y₁ = y₂ ∧ y₁ = y₃ ∧ x = x₂ then
        x
      else
        m
  | m => m

instance rule_projection : IsProj (@rule α _) := sorry

end rw467

namespace rw504

def rule : FreeMagma α → FreeMagma α
  | m@(y₁ ⋆ (y₂ ⋆ (x ⋆ (y₃ ⋆ y₄)))) =>
      if y₁ = y₂ ∧ y₁ = y₃ ∧ y₁ = y₄ then
        x
      else
        m
  | m => m

instance rule_projection : IsProj (@rule α _) := sorry

end rw504

namespace rw1515

def rule : FreeMagma α → FreeMagma α
  | m@((y₁ ⋆ y₂) ⋆ (x ⋆ (x₁ ⋆ x₂))) =>
      if y₁ = y₂ ∧ x = x₁ ∧ x = x₂ then
        x
      else
        m
  | m => m

instance rule_projection : IsProj (@rule α _) := sorry

end rw1515

namespace rw2038

def rule : FreeMagma α → FreeMagma α
  | m@(((x ⋆ x₁) ⋆ x₂) ⋆ (y₁ ⋆ y₂)) =>
      if y₁ = y₂ ∧ x = x₁ ∧ x = x₂ then
        x
      else
        m
  | m => m

instance rule_projection : IsProj (@rule α _) := sorry

end rw2038

namespace rw3140

def rule : FreeMagma α → FreeMagma α
  | m@((((y₁ ⋆ y₂) ⋆ x) ⋆ x₁) ⋆ y₃) =>
      if y₁ = y₂ ∧ y₁ = y₃ ∧ x = x₁ then
        x
      else
        m
  | m => m

instance rule_projection : IsProj (@rule α _) := sorry

end rw3140

namespace rw3143

def rule : FreeMagma α → FreeMagma α
  | m@((((y₁ ⋆ y₂) ⋆ x) ⋆ y₃) ⋆ y₄) =>
      if y₁ = y₂ ∧ y₁ = y₃ ∧ y₁ = y₄ then
        x
      else
        m
  | m => m

instance rule_projection : IsProj (@rule α _) := sorry

end rw3143

namespace rw3150

def rule : FreeMagma α → FreeMagma α
  | m@((((y₁ ⋆ y₂) ⋆ y₃) ⋆ x) ⋆ y₄) =>
      if y₁ = y₂ ∧ y₁ = y₃ ∧ y₁ = y₄ then
        x
      else
        m
  | m => m

instance rule_projection : IsProj (@rule α _) := sorry

end rw3150

namespace rw1110

def rule : FreeMagma α → FreeMagma α
  | m@(y₁ ⋆ ((y₂ ⋆ (x ⋆ x₁)) ⋆ y₃)) =>
      if y₁ = y₂ ∧ y₁ = y₃ ∧ x = x₁ then
        x
      else
        m
  | m => m

instance rule_projection : IsProj (@rule α _) := sorry

end rw1110

namespace rw1086

def rule : FreeMagma α → FreeMagma α
  | m@(y₁ ⋆ ((x ⋆ (y₂ ⋆ y₃)) ⋆ y₄)) =>
      if y₁ = y₂ ∧ y₁ = y₃ ∧ y₁ = y₄ then
        x
      else
        m
  | m => m

instance rule_projection : IsProj (@rule α _) := sorry

end rw1086

namespace rw2497

def rule : FreeMagma α → FreeMagma α
  | m@((y₁ ⋆ (((x ⋆ x₁) ⋆ y₂))) ⋆ y₃) =>
      if y₁ = y₂ ∧ y₁ = y₃ ∧ x = x₁ then
        x
      else
        m
  | m => m

instance rule_projection : IsProj (@rule α _) := sorry

end rw2497

namespace rw2541

def rule : FreeMagma α → FreeMagma α
  | m@((y₁ ⋆ (((y₂ ⋆ y₃) ⋆ x))) ⋆ y₄) =>
      if y₁ = y₂ ∧ y₁ = y₃ ∧ y₁ = y₄ then
        x
      else
        m
  | m => m

instance rule_projection : IsProj (@rule α _) := sorry

end rw2541
