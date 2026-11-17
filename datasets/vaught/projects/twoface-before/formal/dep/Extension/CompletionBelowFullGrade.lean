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
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Ordinal.Arithmetic
import dep.Extension.Apex
import dep.Extension.Basic
import dep.Extension.CoatomAmalgam
import dep.Extension.CoatomScheme
import dep.Extension.Merge
import dep.Extension.PinnedExtension
import dep.Extension.Seed
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

open Finset Label

/-- The **completion below the full grade** of a seed `I`: a scheme on `m + 2` points extending the
amalgam of `I` by cells of full scope only, legal below the full grade, with a lawful labelling
extending the glued labelling of the amalgam.  Its labels need not lie at the stage.  It has the
shape of the completion of [Kni26, Definition 4.3.14] below the full grade (the old cells kept,
the new cells of full scope), not necessarily its rows. -/
structure CompletionBelowFullGrade {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m) where
  /-- The completed scheme: cells, scopes, grades, faces, and rows, on `m + 2` points. -/
  scheme : Scheme.{u} (m + 2)
  /-- The old cells: the cells of the amalgam, in their order. -/
  embed : Fin I.amalgam.card ↪o Fin scheme.card
  /-- The old cells form a lower embedding of the amalgam: grades and the graded order are kept,
  and every cell below an old cell is old. -/
  isLowerEmbedding : I.amalgam.toCellScheme.IsLowerEmbedding scheme.toCellScheme embed
  /-- The old cells keep their scopes. -/
  scope_embed (d : Fin I.amalgam.card) : scheme.toCellScheme.scope (embed d) =
    I.amalgam.toCellScheme.scope d
  /-- The old cells keep their rows: the rows pull back to those of the amalgam. -/
  comap_rows : scheme.rows.comap isLowerEmbedding = I.amalgam.rows
  /-- Every cell of scope other than the ground set is old; the new cells have full scope. -/
  mem_range_embed (z : Fin scheme.card) :
    scheme.toCellScheme.scope z ≠ univ → z ∈ Set.range embed
  /-- The faces are those of the amalgam. -/
  faces_eq : scheme.toCellScheme.faces = I.amalgam.toCellScheme.faces
  /-- The scheme is legal below the full grade `m + 2`.  For the completion, consistency is the
  statement of [Kni26, Lemma 4.3.16] and bountifulness that of [Kni26, Lemma 4.3.20]. -/
  isLegalBelowFullGrade : scheme.IsLegalBelowFullGrade
  /-- The labelling of the cells, not necessarily at the stage. -/
  label : Fin scheme.card → Label.{u}
  /-- The labelling is a lawful section of the rows. -/
  isLawful : scheme.rows.IsLawful label
  /-- The old cells keep the glued labels of the amalgam. -/
  label_embed (d : Fin I.amalgam.card) : label (embed d) = I.amalgam.label d

namespace CompletionBelowFullGrade

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} (F : CompletionBelowFullGrade I)
  {q : Fin F.scheme.card → Label.{u}}

variable (hα : Order.IsSuccPrelimit α)

end CompletionBelowFullGrade

namespace StageType

variable {α : Ordinal.{u}}

end StageType

end VaughtConjecture
