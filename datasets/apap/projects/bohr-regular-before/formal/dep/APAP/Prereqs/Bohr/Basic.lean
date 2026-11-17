module

public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Tactic.NoncommRing

@[expose] public section

open AddChar Function

open scoped NNReal ENNReal Finset

/-- A *Bohr set* `B` on an additive group `G` is a finite set of characters of `G`, called the
*frequencies*, along with an extended non-negative real number for each frequency `ψ`, called the
*width of `B` at `ψ`*.

A Bohr set `B` is thought of as the set `{x | ∀ ψ ∈ B.frequencies, ‖1 - ψ x‖ ≤ B.width ψ}`. This is
the *chord-length* convention. The arc-length convention would instead be
`{x | ∀ ψ ∈ B.frequencies, |arg (ψ x)| ≤ B.width ψ}`.

Note that this set **does not** uniquely determine `B` (in particular, it does not uniquely
determine either `B.frequencies` or `B.width`). -/
@[ext]
structure BohrSet (G : Type*) [AddCommGroup G] where
  frequencies : Finset (AddChar G ℂ)
  /-- The width of a Bohr set at a frequency. Note that this width corresponds to chord-length. -/
  ewidth : AddChar G ℂ → ℝ≥0∞
  mem_frequencies : ∀ ψ, ψ ∈ frequencies ↔ ewidth ψ < ⊤

namespace BohrSet

variable {G : Type*} [AddCommGroup G] {B : BohrSet G} {ψ : AddChar G ℂ} {x : G}

lemma ewidth_injective : Function.Injective (BohrSet.ewidth (G := G)) := sorry

/-- The set corresponding to a Bohr set `B` is `{x | ∀ ψ ∈ B.frequencies, ‖1 - ψ x‖ ≤ B.width ψ}`.
This is the *chord-length* convention. The arc-length convention would instead be
`{x | ∀ ψ ∈ B.frequencies, |arg (ψ x)| ≤ B.width ψ}`.

Note that this set **does not** uniquely determine `B`. -/
@[coe] def chordSet (B : BohrSet G) : Set G := {x | ∀ ψ, ‖1 - ψ x‖₊ ≤ B.ewidth ψ}

/-- Given the Bohr set `B`, `B.Elem` is the `Type` of elements of `B`. -/
@[coe, reducible] def Elem (B : BohrSet G) : Type _ := B.chordSet

instance instCoe : Coe (BohrSet G) (Set G) := ⟨chordSet⟩

instance instCoeSort : CoeSort (BohrSet G) (Type _) := ⟨Elem⟩

noncomputable instance : Max (BohrSet G) where
  max B₁ B₂ :=
    { frequencies := B₁.frequencies ∩ B₂.frequencies,
      ewidth := fun ψ => B₁.ewidth ψ ⊔ B₂.ewidth ψ,
      mem_frequencies := fun ψ => sorry }

noncomputable instance : Min (BohrSet G) where
  min B₁ B₂ := {
    frequencies := B₁.frequencies ∪ B₂.frequencies,
    ewidth ψ := B₁.ewidth ψ ⊓ B₂.ewidth ψ,
    mem_frequencies ψ := sorry
  }

noncomputable instance [Finite G] : Bot (BohrSet G) where
  bot.frequencies := ⊤
  bot.ewidth := 0
  bot.mem_frequencies := sorry

noncomputable instance : Top (BohrSet G) where
  top.frequencies := ⊥
  top.ewidth := ⊤
  top.mem_frequencies := sorry

instance : Preorder (BohrSet G) := .lift ewidth

noncomputable instance : DistribLattice (BohrSet G) :=
  ewidth_injective.distribLattice BohrSet.ewidth .rfl .rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

noncomputable instance : OrderTop (BohrSet G) := OrderTop.lift BohrSet.ewidth (fun _ _ h => h) rfl

open scoped Classical in
noncomputable instance [Finite G] : SupSet (BohrSet G) where
  sSup B := {
    frequencies := {ψ | ⨆ i ∈ B, i.ewidth ψ < ⊤},
    ewidth ψ := ⨆ i ∈ B, ewidth i ψ
    mem_frequencies := sorry
  }

open scoped Classical in
noncomputable instance [Finite G] : InfSet (BohrSet G) where
  sInf B := {
    frequencies := {ψ | ∃ i ∈ B, i.ewidth ψ < ⊤},
    ewidth ψ := ⨅ i ∈ B, ewidth i ψ
    mem_frequencies := sorry
  }

noncomputable instance [Finite G] : CompleteLattice (BohrSet G) :=
  ewidth_injective.completeLattice BohrSet.ewidth .rfl .rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun B ↦ sorry)
    (fun B ↦ sorry)
    rfl
    rfl

noncomputable instance [Finite G] : CompletelyDistribLattice (BohrSet G) := by
  refine .ofMinimalAxioms <| ewidth_injective.completelyDistribLatticeMinimalAxioms .of ewidth ?_ ?_
    <;> · intros; ext; simp only [iSup_apply, iInf_apply]; rfl

/-- The rank of a Bohr set is the number of characters which have finite width. -/
def rank (B : BohrSet G) : ℕ := #B.frequencies

section smul

variable {ρ : ℝ}

noncomputable instance instSMul : SMul ℝ (BohrSet G) where
  smul ρ B := BohrSet.mk B.frequencies
      (fun ψ => if ψ ∈ B.frequencies then Real.nnabs ρ * B.ewidth ψ else ⊤) fun ψ => sorry

noncomputable instance instMulAction : MulAction ℝ (BohrSet G) where
  one_smul B := sorry
  mul_smul ρ φ B := sorry

end smul

open Pointwise

end BohrSet
