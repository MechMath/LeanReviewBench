import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Equiv.Basic
import dep.equational_theories.FreeMagma
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw

open FreeMagma

open Law

def RelOfLaws {α} (β) (Γ : Ctx α) : FreeMagma β → FreeMagma β → Prop :=
  λ t u ↦ Nonempty (Γ ⊢' t ≃ u)

theorem RelOfLaws.isEquivalence {α} (β) (Γ : Ctx α) : Equivalence (RelOfLaws β Γ) := sorry

def SetoidOfLaws {α} (β) (Γ : Ctx α) : Setoid (FreeMagma β) :=
  ⟨ RelOfLaws β Γ, RelOfLaws.isEquivalence β Γ ⟩

theorem SetoidOfLaws.iff {α} (β) (Γ : Ctx α) (x y : FreeMagma β) :
    let _ := SetoidOfLaws β Γ; x ≈ y ↔ Nonempty (Γ ⊢' x ≃ y) := sorry

def FreeMagmaWithLaws.{u} {α} (β : Type u) (Γ : Ctx α) : Type u := Quotient (SetoidOfLaws β Γ)

def embed {α β} (Γ : Ctx α) (x : FreeMagma β) : FreeMagmaWithLaws β Γ := Quotient.mk _ x

theorem FreeMagmaWithLaws.eq {α β} {Γ : Ctx α} {x y : FreeMagma β} :
    embed Γ x = embed Γ y ↔ Nonempty (Γ ⊢' x ≃ y) := sorry

def ForkWithLaws {α β} {Γ : Ctx α} :
    FreeMagmaWithLaws β Γ → FreeMagmaWithLaws β Γ → FreeMagmaWithLaws β Γ :=
  Quotient.lift₂ (λ x y ↦ embed Γ (x ⋆ y)) <| sorry

protected instance FreeMagmaWithLaws.Magma {α} (β) (Γ : Ctx α) : Magma (FreeMagmaWithLaws β Γ) :=
  { op := ForkWithLaws }

instance {G} [Magma G] : Magma (ULift G) where
  op x y := .up (x.down ◇ y.down)
