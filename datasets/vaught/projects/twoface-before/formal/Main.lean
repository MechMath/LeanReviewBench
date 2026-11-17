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
import dep.Extension.Tower
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

namespace VaughtConjecture.Seed

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)

end VaughtConjecture.Seed

namespace VaughtConjecture.StageType

/-- **The coatom extension property with apex under the two-face lift at the grades `2 ≤ j < m`**:
at a stage `α` that is zero or a limit, if every seed on `m + 2` points satisfies `2FL(j)` at the
grades `2 ≤ j < m`, then every seed has a completion below the full grade
(`Seed.nonempty_completionBelowFullGrade_of_twoFaceLift`), and so
(`StageType.HasApexCoatomExtensions.of_completionBelowFullGrade`) any two legal coatom types with
the same face are the faces of one legal stage type with an apex. -/
theorem hasApexCoatomExtensions_of_twoFaceLift {α : Ordinal.{u}} (hα : Order.IsSuccPrelimit α)
    (h2 : ∀ (m : ℕ) (I : Seed.{u} α m) (j : ℕ), 2 ≤ j → j < m → I.TwoFaceLift j) :
    HasApexCoatomExtensions.{u} α := sorry

end VaughtConjecture.StageType
