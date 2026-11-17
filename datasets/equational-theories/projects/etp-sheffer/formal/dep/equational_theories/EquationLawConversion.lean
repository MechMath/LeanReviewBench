import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Equiv.Basic
import dep.equational_theories.FreeMagma
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw

open Law

def FreeMagma.evalBounded {G} [Magma G] (ls : List G) :
    (m : FreeMagma Nat) → (∀ a, m.Mem a → a < ls.length) → G
  | a ⋆ b, h => a.evalBounded ls (h · ∘ .inl) ◇ b.evalBounded ls (h · ∘ .inr)
  | Lf a, h => ls.get ⟨a, h _ rfl⟩

def Law.MagmaLaw.evalBounded {G} [Magma G] (ls : List G) :
    (m : NatMagmaLaw) → (∀ a, m.Mem a → a < ls.length) → Prop
  | ⟨a, b⟩, h => a.evalBounded ls (h · ∘ .inl) = b.evalBounded ls (h · ∘ .inr)

def FreeMagma.bounded (n : Nat) : FreeMagma Nat → Bool
  | a ⋆ b => a.bounded n && b.bounded n
  | Lf a => a < n

def Law.MagmaLaw.bounded (n : Nat) : NatMagmaLaw → Bool
  | ⟨a, b⟩ => a.bounded n && b.bounded n

theorem Law.MagmaLaw.bounded_iff {n} {m : NatMagmaLaw} : m.bounded n ↔ ∀ a, m.Mem a → a < n := sorry

def ModelsIffType (G : Type*) [Magma G] (law : NatMagmaLaw) :
    (n : Nat) → (ls : List G) → law.bounded (n + ls.length) → Prop
  | 0, xs, h => law.evalBounded xs.reverse (by simpa using Law.MagmaLaw.bounded_iff.1 h)
  | n+1, xs, h => ∀ x, ModelsIffType G law n (x::xs) (by rwa [Nat.succ_add] at h)

theorem models_iff_n (law : NatMagmaLaw) (n) (h : law.bounded n) (G : Type _) [Magma G] :
    G ⊧ law ↔ ModelsIffType G law n [] h := sorry
