import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
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
import dep.Extension.Basic
import dep.Extension.CoatomAmalgam
import dep.Extension.CoatomScheme
import dep.Extension.Merge
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

/-- A **seed** of the coatom extension at stage `α` on `m + 2` points: two legal coatom stage types
with a common face, their amalgam with its glued labelling and literal coatom faces, and the laws
and face structure of the amalgam [Kni26, Definition 4.3.1 and Lemma 4.3.2]. -/
structure Seed (α : Ordinal.{u}) (m : ℕ) where
  /-- The amalgam, with the glued lawful labelling: a stage type on `m + 2` points. -/
  amalgam : StageType.{u} α (m + 2)
  /-- The stage type on the coatom omitting the last point. -/
  left : StageType.{u} α (m + 1)
  /-- The stage type on the coatom omitting the point `m`. -/
  right : StageType.{u} α (m + 1)
  /-- The common face of the two coatom types, on `m` points. -/
  face : StageType.{u} α m
  /-- The stage type on the first coatom is legal. -/
  isLegal_left : left.IsLegal
  /-- The stage type on the second coatom is legal. -/
  isLegal_right : right.IsLegal
  /-- The face of `left` along `Fin.castSuccEmb` is literally `face`. -/
  restrictFace_face_left : StageType.restrictFace (Coatom.face m) left = some face
  /-- The face of `right` along `Fin.castSuccEmb` is literally `face`. -/
  restrictFace_face_right : StageType.restrictFace (Coatom.face m) right = some face
  /-- The face of the amalgam along `Fin.castSuccEmb` is literally `left`, labels included. -/
  restrictFace_left : StageType.restrictFace (Coatom.left m) amalgam = some left
  /-- The face of the amalgam along `extendByLast Fin.castSuccEmb` is literally `right`, labels
  included. -/
  restrictFace_right : StageType.restrictFace (Coatom.right m) amalgam = some right
  /-- The rows of the amalgam are consistent [Kni26, Lemma 4.3.2]. -/
  isConsistent : amalgam.rows.IsConsistent
  /-- The rows of the amalgam are bountiful [Kni26, Lemma 4.3.2]. -/
  isBountiful : amalgam.rows.IsBountiful
  /-- Every face of the amalgam other than the ground set lies in one of the two coatoms, the
  ground set without the last point or without the point `m`. -/
  subset_or_subset : ∀ B ∈ amalgam.toCellScheme.faces, B ≠ univ →
    B ⊆ univ.erase (Fin.last (m + 1)) ∨ B ⊆ univ.erase (Fin.castSucc (Fin.last m))
  /-- No cell of the amalgam has the full scope. -/
  scope_ne_univ (d : Fin amalgam.card) : amalgam.toCellScheme.scope d ≠ univ
  /-- Every graded face of scope other than the ground set is the graded index of a cell. -/
  exists_gradedIndex_eq : ∀ X ∈ amalgam.toCellScheme.gradedFaces, X.1 ≠ univ →
    ∃ d, amalgam.toCellScheme.gradedIndex d = X

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)

/-- Every cell of the amalgam has grade below `m + 2`: its scope is a proper subset of the `m + 2`
points. -/
theorem grade_lt (d : Fin I.amalgam.card) : I.amalgam.toCellScheme.grade d < m + 2 := sorry

variable {ta tb : StageType.{u} α (m + 1)} {p : StageType.{u} α m}

end Seed

end VaughtConjecture
