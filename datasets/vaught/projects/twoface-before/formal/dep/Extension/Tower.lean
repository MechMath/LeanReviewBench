import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Countable
import Mathlib.Order.InitialSeg
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.SupClosed
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Ordinal.Arithmetic
import dep.Extension.Apex
import dep.Extension.Basic
import dep.Extension.CanonicalCode
import dep.Extension.CoatomAmalgam
import dep.Extension.CoatomScheme
import dep.Extension.Coding
import dep.Extension.CompletionBelowFullGrade
import dep.Extension.FieldLayer
import dep.Extension.Merge
import dep.Extension.OrbitCode
import dep.Extension.PinnedExtension
import dep.Extension.Seed
import dep.Extension.SourcePrefix
import dep.Extension.WitnessAlgebra
import dep.Geometry.ConvexGeometry
import dep.Geometry.Plan
import dep.Label.Basic
import dep.Label.Cap
import dep.Label.OrdinalVisibility
import dep.Label.Transform
import dep.Label.Visibility
import dep.Scheme.Bountiful
import dep.Scheme.Cell
import dep.Scheme.Row
import dep.Scheme.Transport
import dep.Stage.Basic
import dep.Stage.Countable
import dep.Stage.Legal
import dep.Stage.Scheme

universe u

namespace VaughtConjecture

open Finset Label CellScheme

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)

/-- A scheme on `m + 2` points whose cells all have grade at most `j` or scope other than the
ground set lies above no cell at `(univ, j + 1)`. -/
private theorem not_univ_succ_le_of_forall {S : Scheme.{u} (m + 2)} {j : ℕ}
    (hS : ∀ d, S.toCellScheme.grade d ≤ j ∨ S.toCellScheme.scope d ≠ univ) (d : Fin S.card) :
    ¬ ((univ : Finset (Fin (m + 2))), j + 1) ≤ S.toCellScheme.gradedIndex d := sorry

/-- The tower together with the property that makes the next layer defined: every cell of the
scheme at the grade `j` has grade at most `j` or scope other than the ground set. -/
noncomputable def towerAux : (j : ℕ) → {S : Scheme.{u} (m + 2) //
    ∀ d, S.toCellScheme.grade d ≤ j ∨ S.toCellScheme.scope d ≠ univ}
  | 0 => ⟨I.amalgam.toScheme, fun d ↦ .inr (I.scope_ne_univ d)⟩
  | j + 1 => ⟨(towerAux j).1.fieldLayer (j + 1) (not_univ_succ_le_of_forall (towerAux j).2),
      fun d ↦ sorry⟩

/-- The **tower of field layers** of a seed: the scheme `T j` reached after the grade `j`.  It is
the amalgam at `j = 0`, and `T (j + 1)` is the canonical field layer of `T j` at the grade `j + 1`
(`Seed.tower_succ`). -/
noncomputable abbrev tower (j : ℕ) : Scheme.{u} (m + 2) := (I.towerAux j).1

/-- The **old cells** in the scheme reached after the grade `j`: the cells of the amalgam, along
`Fin.castAdd` once for each layer. -/
noncomputable def towerEmbed : (j : ℕ) → Fin I.amalgam.card ↪o Fin (I.tower j).card
  | 0 => RelEmbedding.refl _
  | j + 1 => (towerEmbed j).trans (Fin.castAddOrderEmb ((I.tower j).catalogue (j + 1)).card)

/-- An old cell of grade at most `j` lies below `(univ, j)`. -/
theorem towerEmbed_mem_below {j : ℕ} {d : Fin I.amalgam.card}
    (hd : I.amalgam.toCellScheme.grade d ≤ j) :
    I.towerEmbed j d ∈ (I.tower j).toCellScheme.below (univ, j) := sorry

/-- **The two-face lift `2FL(j)`** of the tower at the grade `j`: for every catalogue entry `a` of
the layer at the grade `j + 1` and every cap `h` self-visible and short at `j + 1` with `⊥ < h`,
every labelling `w` of the amalgam lawful below both coatoms at the grade `j + 1` that agrees with
`a` capped at `h` at the old cells of grade at most `j + 1` extends, unchanged at the old cells of
grade at most `j`, to a labelling lawful below `(univ, j)` in the scheme reached after the grade
`j` that agrees with `a` capped at `h` at every cell below `(univ, j)`.

It is the extension from the boundary that the step to the grade `j + 1` uses at the positive caps
(`Seed.extendsFromBoundary_tower_of_twoFaceLift`), read on the scheme before the layer, and
equivalent to that hypothesis of the step (`Seed.twoFaceLift_iff_extendsFromBoundary`):

* `a` ranges over the catalogue entries at the grade `j + 1`, not over all lawful labellings: the
  ambient at a positive cap is the row of a cell of the new layer, which reads its entry on the
  scheme before (`Scheme.fieldRow_castAdd`);
* `h` ranges over the caps self-visible and short at `j + 1` with `⊥ < h`, the source caps of the
  owner alignment; at the cap `⊥` no ambient enters, and the extension is
  `Seed.exists_isLawfulBelow_tower`.  The cap need not be short at the grades `1, …, j` of the
  layers below `(univ, j)`;
* `w` ranges over the labellings lawful below both coatoms at the grade `j + 1` that agree with `a`
  capped at `h`: in the step it is the aligned encoding of the prescription on one coatom glued
  with its lift into the other coatom, a lift of the amalgam.  The one-grade lift
  (`CellScheme.Rows.cappedLift_of_boundary_short`) asks for the extension along every row of the
  new layer, at every such cap, of every such labelling; the step itself meets only the rows of
  the new cells to which its owner alignments align, the source caps and the glued aligned
  encodings of those alignments.

Lawfulness of `w` at the grade `j + 1`, not only at `j`, is part of the hypothesis: the old cells of
the grade `j + 1` are not below `(univ, j)`, but they constrain `w` below it.

It is not the invariant at the grade `j + 1` in another form.  It concerns the scheme before the
layer at the grade `j + 1` and asserts nothing about the new cells of that grade; it prescribes both
coatoms at once, rather than lifting from one coatom with the other free; it is required only at
the caps short at `j + 1` and along catalogue entries, not at every self-visible cap and ambient;
and its labelling agrees with `a` only capped at `h`, with nothing asserted above `h` on the new
cells.  The invariant at `j + 1` follows from it together with the invariant at `j`, the
restoration of the lower prescriptions, the owner alignment, and the extension through the layer at
`j + 1` (`Seed.towerInvariant_succ`).  At the grade `j = 0`
it holds (`Seed.twoFaceLift_zero`); it is assumed by the step at the grades `2 ≤ j + 1 ≤ m`
(`Seed.towerInvariant_of_twoFaceLift`).  `2FL(1)` holds at every arity (`Seed.twoFaceLift_one`);
`2FL(j)` for `j ≥ 2` is open. -/
def TwoFaceLift (j : ℕ) : Prop :=
  ∀ a ∈ (I.tower j).catalogue (j + 1),
  ∀ h : Label.{u}, IsSelfVisible (j + 1) h → IsShort (j + 1) h → ⊥ < h →
  ∀ w : Fin I.amalgam.card → Label.{u},
    I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.last (m + 1)), j + 1) (fun d ↦ w d) →
    I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last m)), j + 1)
      (fun d ↦ w d) →
    (∀ d, I.amalgam.toCellScheme.grade d ≤ j + 1 →
      min (w d) h = min (a (I.towerEmbed j d)) h) →
    ∃ r : (I.tower j).toCellScheme.below (univ, j) → Label.{u},
      (I.tower j).rows.IsLawfulBelow (univ, j) r ∧
      (∀ d (hd : I.amalgam.toCellScheme.grade d ≤ j),
        r ⟨I.towerEmbed j d, I.towerEmbed_mem_below hd⟩ = w d) ∧
      ∀ e, min (r e) h = min (a e) h

end Seed

namespace TowerExamples

section LiteralFaces

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m) (hα : Order.IsSuccPrelimit α) {j : ℕ}
  (hj : j ≤ m + 2)

end LiteralFaces

end TowerExamples

end VaughtConjecture
