import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Equiv.Basic
import dep.equational_theories.FreeMagma
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma

open FreeMagma

namespace Law

@[ext] structure MagmaLaw (α : Type*) where
  lhs : FreeMagma α
  rhs : FreeMagma α
deriving DecidableEq

infix:60 " ≃ " => MagmaLaw.mk

abbrev NatMagmaLaw := MagmaLaw Nat

open Lean in
instance {α} [ToJson α] : ToJson (MagmaLaw α) where
  toJson := fun ⟨lhs, rhs⟩ => .mkObj [("lhs", Lean.toJson lhs), ("rhs", Lean.toJson rhs)]

instance {α} [ToString α] : ToString (MagmaLaw α) where
  toString := fun ⟨lhs, rhs⟩ => s!"{lhs} ≃ {rhs}"

end Law

open Law

abbrev Ctx α := Set (MagmaLaw α)

instance Ctx.Membership α : Membership (MagmaLaw α) (Ctx α) := ⟨ Set.instMembership.mem ⟩

instance {α : Type} : Singleton (MagmaLaw α) (Ctx α) := ⟨Set.singleton⟩

section DeriveDef

set_option hygiene false

/-- Local Notation for derivability -/
local infix:50 " ⊢ " =>  derive

/-- Definition for derivability -/
inductive derive.{u} {α : Type u} (Γ : Ctx α) : MagmaLaw α → Type u where
  | Ax {E} (h : E ∈ Γ) : Γ ⊢ E
  | Ref {t} : Γ ⊢ t ≃ t
  | Sym {t u} : Γ ⊢ t ≃ u → Γ ⊢ u ≃ t
  | Trans {t u v} : Γ ⊢ t ≃ u → Γ ⊢ u ≃ v → Γ ⊢ t ≃ v
  -- This is not as polymorphic as it could be, shouldn't be an issue at the moment
  | Subst {t u} σ : Γ ⊢ t ≃ u → Γ ⊢ t ⬝ σ ≃ u ⬝ σ
  | Cong {t₁ t₂ u₁ u₂} : Γ ⊢ (t₁ ≃ t₂) → Γ ⊢ (u₁ ≃ u₂) → Γ ⊢ (t₁ ⋆ u₁ ≃ t₂ ⋆ u₂)

local infix:50 " ⊢' " =>  derive'

/-- Definition for derivability where Subst can only be applied to Ax -/
inductive derive'.{u, v} {α : Type u} {β : Type v} (Γ : Ctx α) : MagmaLaw β → Type (max u v) where
  | SubstAx {E} (h : E ∈ Γ) (σ) : Γ ⊢' E.lhs ⬝ σ ≃ E.rhs ⬝ σ
  | Ref {t} : Γ ⊢' t ≃ t
  | Sym {t u} : Γ ⊢' t ≃ u → Γ ⊢' u ≃ t
  | Trans {t u v} : Γ ⊢' t ≃ u → Γ ⊢' u ≃ v → Γ ⊢' t ≃ v
  | Cong {t₁ t₂ u₁ u₂} : Γ ⊢' t₁ ≃ t₂ → Γ ⊢' u₁ ≃ u₂ → Γ ⊢' t₁ ⋆ u₁ ≃ t₂ ⋆ u₂

end DeriveDef

/-- Definitions of entailment -/
def satisfiesPhi {α G} [Magma G] (φ : α → G) (E : MagmaLaw α) : Prop :=
  E.lhs ⬝ φ = E.rhs ⬝ φ

/-- `satisfies G E`, or `G ⊧ E`, means that all evaluations of `E` in `G` are true. -/
def satisfies {α} (G) [Magma G] (E : MagmaLaw α) := ∀ (φ : α → G), satisfiesPhi φ E

/-- `satisfiesSet G Γ`, or `G ⊧ Γ`, means that `G` satisfies every element of `Γ`. -/
def satisfiesSet {α} (G) [Magma G] (Γ : Ctx α) : Prop :=
  ∀ E ∈ Γ, satisfies G E

/-- `models Γ E`, or `Γ ⊧ E`, means that every magma `G` satisfying `Γ` also satisfies `E`. -/
def models {α β} (Γ : Ctx α) (E : MagmaLaw β) : Prop :=
  ∀ (G : Type) [Magma G], satisfiesSet G Γ → satisfies G E

@[inherit_doc] infix:50 " ⊧ " => satisfies

@[inherit_doc] infix:50 " ⊧ " => satisfiesSet

@[inherit_doc] infix:50 " ⊧ " => models

@[inherit_doc] infix:50 " ⊢ " => derive

@[inherit_doc] infix:50 " ⊢' " => derive'

namespace Law

namespace MagmaLaw

def symm {α} (l : MagmaLaw α) : MagmaLaw α := {lhs := l.rhs, rhs := l.lhs}

def map {α β} (f : α → β) : MagmaLaw α → MagmaLaw β
  | ⟨lhs, rhs⟩ => ⟨fmapHom f lhs, fmapHom f rhs⟩

def Mem {α} (a : α) (m : MagmaLaw α) : Prop :=
  m.lhs.Mem a ∨ m.rhs.Mem a

def toList {α} (m : MagmaLaw α) : List α := m.lhs.toList ++ m.rhs.toList

def elems {α} [DecidableEq α] (m : MagmaLaw α) :
    {l : List α // l.Nodup ∧ ∀ a, a ∈ l ↔ Mem a m} := by
  let ⟨l, _, hl⟩ := m.lhs.elems
  let ⟨r, nr, hr⟩ := m.rhs.elems
  use l ∪ r, .union _ nr; simp [Mem, hl, hr]

instance {α} [DecidableEq α] (a : α) (m : MagmaLaw α) : Decidable (Mem a m) :=
  decidable_of_iff _ (m.elems.2.2 _)

def finEquiv {α} [DecidableEq α] (m : MagmaLaw α) : Fin m.elems.1.length ≃ {a // Mem a m} := by
  convert ← m.elems.2.1.getEquiv; apply m.elems.2.2

def pmap {α β} : ∀ (m : MagmaLaw α), (∀ a, Mem a m → β) → MagmaLaw β
  | ⟨lhs, rhs⟩, f =>
    ⟨lhs.pmap fun a h => f a (.inl h), rhs.pmap fun a h => f a (.inr h)⟩

def attach {α} (m : MagmaLaw α) : MagmaLaw {a // Mem a m} := pmap m .mk

def toFin {α} [DecidableEq α] (m : MagmaLaw α) : MagmaLaw (Fin m.elems.1.length) :=
  m.attach.map (finEquiv m).symm

def toNat {α} [DecidableEq α] (m : MagmaLaw α) : MagmaLaw ℕ :=
  (toFin m).map (·.val)

end MagmaLaw

end Law
