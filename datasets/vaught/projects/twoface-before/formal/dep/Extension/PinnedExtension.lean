import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Order.InitialSeg
import Mathlib.Order.SupClosed
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Ordinal.Arithmetic
import dep.Extension.Basic
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

open Finset

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n}

end Scheme

namespace StageType

variable {α : Ordinal.{u}} {n m k : ℕ}

variable (α) in
/-- The **coatom extension property with apex** at stage `α`: [Kni26, Corollary 4.3.22] in full,
in the arrangement used for pinned extensions.  Any two legal stage types `ta` and `tb` on `m + 1`
points with the same face along `Fin.castSuccEmb` are the faces, along `Fin.castSuccEmb` and
`extendByLast Fin.castSuccEmb`, of one legal stage type `t` on `m + 2` points which moreover has a
cell `Ξ` of full scope and full grade `m + 2` carrying the largest label of `t`,
`q(Ξ) = max ran q`.

This is an existence statement, a hypothesis and not a theorem, while the completion of the amalgam
of `VaughtConjecture.Extension.CoatomAmalgam` is not constructed; it is the form in which the
completion is to be proved, and the apex is what high-arity dominance [Kni26, Lemma 4.4.3] uses. -/
def HasApexCoatomExtensions : Prop :=
  ∀ (m : ℕ) (ta tb : StageType.{u} α (m + 1)) (p : StageType.{u} α m), ta.IsLegal → tb.IsLegal →
    restrictFace Fin.castSuccEmb ta = some p → restrictFace Fin.castSuccEmb tb = some p →
    ∃ t : StageType.{u} α (m + 2), t.IsLegal ∧ restrictFace Fin.castSuccEmb t = some ta ∧
      restrictFace (extendByLast Fin.castSuccEmb) t = some tb ∧
      ∃ d, t.toCellScheme.gradedIndex d = (univ, m + 2) ∧ ∀ e, t.label e ≤ t.label d

end StageType

end VaughtConjecture
