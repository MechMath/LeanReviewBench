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

namespace VaughtConjecture.Scheme

open Finset Label

variable {n : ℕ} (S : Scheme.{u} n) (k M : ℕ)

/-- The cell scheme of `S` with `M` more cells, last, of scope `univ` and grade `k`. -/
def appendFullCellsScheme : CellScheme (Fin (S.card + M)) (Fin n) where
  ground := S.toCellScheme.ground
  faces := S.toCellScheme.faces
  scope := Fin.append S.toCellScheme.scope fun _ ↦ univ
  grade := Fin.append S.toCellScheme.grade fun _ ↦ k

/-- An old cell keeps its scope. -/
@[simp] theorem appendFullCellsScheme_scope_castAdd (d : Fin S.card) :
    (S.appendFullCellsScheme k M).scope (Fin.castAdd M d) = S.toCellScheme.scope d := sorry

/-- An old cell keeps its grade. -/
@[simp] theorem appendFullCellsScheme_grade_castAdd (d : Fin S.card) :
    (S.appendFullCellsScheme k M).grade (Fin.castAdd M d) = S.toCellScheme.grade d := sorry

/-- A new cell has grade `k`. -/
@[simp] theorem appendFullCellsScheme_grade_natAdd (i : Fin M) :
    (S.appendFullCellsScheme k M).grade (Fin.natAdd S.card i) = k := sorry

variable {S k M}

/-- Below a pair that is not above `(univ, k)`, every cell is old. -/
theorem lt_card_of_mem_below {X : Finset (Fin n) × ℕ} (hX : ¬ ((univ : Finset (Fin n)), k) ≤ X)
    {d : Fin (S.card + M)} (hd : d ∈ (S.appendFullCellsScheme k M).below X) :
    (d : ℕ) < S.card := sorry

/-- No new cell lies below an old cell, when no cell of `S` lies above `(univ, k)`. -/
theorem not_le_gradedIndex_of_lt
    (h : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d)
    {s : Fin (S.card + M)} (hs : (s : ℕ) < S.card) :
    ¬ ((univ : Finset (Fin n)), k) ≤ (S.appendFullCellsScheme k M).gradedIndex s := sorry

/-- The cells below an old cell are old, and lie below it in `S`. -/
theorem mem_below_of_lt
    (h : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d)
    {s : Fin (S.card + M)} (hs : (s : ℕ) < S.card)
    (t : (S.appendFullCellsScheme k M).below ((S.appendFullCellsScheme k M).gradedIndex s)) :
    (⟨t.1, lt_card_of_mem_below (not_le_gradedIndex_of_lt h hs) t.2⟩ : Fin S.card) ∈
      S.toCellScheme.below (S.toCellScheme.gradedIndex ⟨s, hs⟩) := sorry

variable (S k M) in
/-- **Appending cells of full scope**: the scheme with the cells of `S`, in their order, followed
by `M` cells of scope `univ` and grade `k`, the `i`-th with row `r i` (a labelling of all cells,
read on those below `(univ, k)`).  The hypothesis says that no cell of `S` lies above `(univ, k)`,
so that the old rows, which are those of `S`, see only old cells.

It is an `abbrev`, not a `def`, for the reason recorded at `Scheme.appendFullCell`: its number of
cells must unfold reducibly to `S.card + M`, so that `Fin.castAdd` and `Fin.natAdd` apply to its
cells in rewriting and in `simp`. -/
abbrev appendFullCells (r : Fin M → Fin (S.card + M) → Label.{u})
    (h : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d) : Scheme.{u} n where
  card := S.card + M
  toCellScheme := S.appendFullCellsScheme k M
  rows := ⟨fun s t ↦ if hs : (s : ℕ) < S.card then
      S.rows.row ⟨s, hs⟩ ⟨⟨t.1, lt_card_of_mem_below (not_le_gradedIndex_of_lt h hs) t.2⟩,
        mem_below_of_lt h hs t⟩
    else r ⟨s - S.card, sorry⟩ t.1⟩

variable {r : Fin M → Fin (S.card + M) → Label.{u}}
  {h : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}

end VaughtConjecture.Scheme

namespace VaughtConjecture.Scheme

open Finset Label

variable {n : ℕ} (S : Scheme.{u} n) (k : ℕ)

/-- The grid of the field layer at grade `k`: block bound `2 N + 2` for `N` old cells. -/
noncomputable abbrev fieldGrid : Finset Label.{u} := grid k (2 * S.card + 2)

open Classical in
/-- The **canonical catalogue** at grade `k`: the lawful labellings of the cells of `S` that are
bottom at the cells of grade above `k` and orbit-canonical, fixed by the orbit code.  They take
values in the code grid with block bound `2 N`. -/
noncomputable def catalogue : Finset (Fin S.card → Label.{u}) :=
  {a ∈ Fintype.piFinset fun _ ↦ codeGrid k (2 * S.card) | S.rows.IsLawful a ∧
    (∀ d, k < S.toCellScheme.grade d → a d = ⊥) ∧ orbitCode k a = a}

variable {S k}

variable (S k) in
/-- The catalogue entry of the new cell `i`. -/
noncomputable def catalogueEntry (i : Fin (S.catalogue k).card) : Fin S.card → Label.{u} :=
  ((S.catalogue k).equivFin.symm i).1

variable (S k) in
/-- The **field row** of a labelling `a` of the old cells: `a` on the old cells, and on the new
cell `j` the agreement height of `a` with its catalogue entry. -/
noncomputable def fieldRow (a : Fin S.card → Label.{u}) :
    Fin (S.card + (S.catalogue k).card) → Label.{u} :=
  Fin.append a fun j ↦ agreementHeight (S.fieldGrid k) a (S.catalogueEntry k j)

variable (S k) in
/-- **The canonical field layer** at grade `k`: the cells of `S`, followed by one cell of scope
`univ` and grade `k` for each entry of the canonical catalogue, whose row is the field row of the
entry. -/
noncomputable abbrev fieldLayer
    (hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d) : Scheme.{u} n :=
  S.appendFullCells k (S.catalogue k).card (fun i ↦ S.fieldRow k (S.catalogueEntry k i)) hS

variable {hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}

variable {U V : Finset (Fin n) × ℕ}

end VaughtConjecture.Scheme
