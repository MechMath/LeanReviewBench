import Mathlib.SetTheory.Ordinal.Arithmetic
import dep.Label.Basic
import dep.Label.OrdinalVisibility
import dep.Label.Visibility

universe u

namespace VaughtConjecture.Label

variable {D D' : Type*} {grade : D → ℕ} {p q : D → Label.{u}}
  {g g' : ℕ → Label.{u}} {σ τ ν : Label.{u} → Label.{u}}

/-- The laws of a transformation witness: a suppressor `g` and a shifter `σ`
[Kni26, Definition 2.3.9]. -/
structure IsWitness (g : ℕ → Label.{u}) (σ : Label.{u} → Label.{u}) : Prop where
  /-- The suppressor is antitone. -/
  antitone : Antitone g
  /-- Each value of the suppressor is self-visible at its grade. -/
  isSelfVisible : ∀ n, IsSelfVisible n (g n)
  /-- The shifter fixes bottom. -/
  map_bot : σ ⊥ = ⊥
  /-- The shifter is monotone. -/
  monotone : Monotone σ
  /-- Under the guard `σ x ≤ g k`, the shifter commutes with visibility replacement at
  threshold `k` for every value `i ≤ k`. -/
  visibilityReplace_comm : ∀ x k, σ x ≤ g k → ∀ i ≤ k,
    σ (visibilityReplace k i x) = visibilityReplace k i (σ x)

/-- The labelling `p` *transforms to* `q` over the grades `grade`: for some witness `(g, σ)`,
`q d = min (σ (p d)) (g (grade d))` for every cell `d`. -/
def TransformsTo (grade : D → ℕ) (p q : D → Label.{u}) : Prop :=
  ∃ g σ, IsWitness g σ ∧ ∀ d, q d = min (σ (p d)) (g (grade d))

/-- Every labelling transforms to itself. -/
theorem TransformsTo.refl (grade : D → ℕ) (p : D → Label.{u}) : TransformsTo grade p p := sorry

/-- A transformation pulls back along any map of cell families. -/
theorem TransformsTo.reindex (h : TransformsTo grade p q) (φ : D' → D) :
    TransformsTo (grade ∘ φ) (p ∘ φ) (q ∘ φ) := sorry

/-- A transformation preserves self-visibility of a label at the grade of its cell. -/
theorem TransformsTo.isSelfVisible (h : TransformsTo grade p q) {d : D}
    (hp : IsSelfVisible (grade d) (p d)) : IsSelfVisible (grade d) (q d) := sorry

/-- The pointwise maximum of two suppressors of a shifter is a suppressor of it. -/
theorem IsWitness.sup (hg : IsWitness g σ) (hg' : IsWitness g' σ) : IsWitness (g ⊔ g') σ := sorry

section Collapse

variable {β : Ordinal.{u}} {N : ℕ} {x y : Label.{u}}

end Collapse

section Nontransitive

open Ordinal

end Nontransitive

end VaughtConjecture.Label
