import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Equiv.Basic
import dep.equational_theories.FreeMagma
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw

open Law

namespace Law.MagmaLaw

variable {α β γ : Type*}

/--
A magma law `l₁` implies a law `l₂` if in any Magma `G` where `l₁` holds, `l₂` also holds.

We have to explicitly quantify the type `G` and the Magma instance `[Magma G]` instead of
using them as parameters so that the implication holds in any Magma `G`.
-/
def implies (l₁ : MagmaLaw α) (l₂ : MagmaLaw β) := ∀ {{G : Type}} [Magma G],
  satisfies G l₁ → satisfies G l₂

protected def iff (l₁ : MagmaLaw α) (l₂ : MagmaLaw β) := ∀ (G : Type) [Magma G],
  satisfies G l₁ ↔ satisfies G l₂

theorem iff.symm {l₁ : MagmaLaw α} {l₂ : MagmaLaw β} (h : l₁.iff l₂) :
    l₂.iff l₁ := sorry

theorem iff.mp {l₁ : MagmaLaw α} {l₂ : MagmaLaw β} (h : l₁.iff l₂) :
    l₁.implies l₂ := sorry

theorem iff.mpr {l₁ : MagmaLaw α} {l₂ : MagmaLaw β} (h : l₁.iff l₂) :
    l₂.implies l₁ := sorry

/--
If a law `l₁` implies a law `l₂`, then we say `l₁ ≤ l₂`.
-/
instance : LE (MagmaLaw α) where
  le l₁ l₂ := l₁.implies l₂

theorem implies_refl (l : MagmaLaw α) : l ≤ l := sorry

theorem implies_trans {l₁ l₂ l₃ : MagmaLaw α} : l₁ ≤ l₂ → l₂ ≤ l₃ → l₁ ≤ l₃ := sorry

instance : Preorder (MagmaLaw α) where
  le_refl := implies_refl
  le_trans := fun _ _ _ ↦ implies_trans

end Law.MagmaLaw
