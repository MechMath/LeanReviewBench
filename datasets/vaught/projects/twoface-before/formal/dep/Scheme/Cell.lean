import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Set.Countable
import Mathlib.Order.InitialSeg
import Mathlib.Order.SupClosed
import dep.Geometry.ConvexGeometry
import dep.Geometry.Plan

namespace VaughtConjecture

open Finset

variable {ι κ α β : Type*}

/-- A **cell scheme**: the raw data of a finite ground set, a finite family of closed faces, and a
family of cells indexed by `ι`, each with a scope and a grade.  The laws, including the finiteness
of the family of cells, are `CellScheme.IsWellFormed`. -/
@[ext]
structure CellScheme (ι α : Type*) where
  /-- The ground set. -/
  ground : Finset α
  /-- The closed faces (the plan). -/
  faces : Finset (Finset α)
  /-- The scope of each cell. -/
  scope : ι → Finset α
  /-- The grade of each cell. -/
  grade : ι → ℕ

namespace CellScheme

variable (D : CellScheme ι α) {E : CellScheme κ β} {X Y : Finset α × ℕ} {d s t : ι}

/-- The graded index of a cell: its scope and grade. -/
def gradedIndex (d : ι) : Finset α × ℕ := (D.scope d, D.grade d)

/-- The *graded faces* of a scheme: the pairs `(B, j)` of a closed face `B` and a grade
`0 < j ≤ |B|`. -/
def gradedFaces : Set (Finset α × ℕ) := {X | X.1 ∈ D.faces ∧ 0 < X.2 ∧ X.2 ≤ #X.1}

/-- The laws of a cell scheme: there are finitely many cells, the faces form a plan on the ground
set, and the graded index of every cell is a graded face (its scope is closed and its grade lies
in `[1, |scope|]`). -/
structure IsWellFormed [DecidableEq α] : Prop where
  /-- There are finitely many cells. -/
  finite : Finite ι
  /-- The faces form a recursive visible-face plan on the ground set. -/
  isPlan : Geometry.IsPlan D.ground D.faces
  /-- Every cell has a closed scope and a grade between one and the size of its scope. -/
  gradedIndex_mem (d : ι) : D.gradedIndex d ∈ D.gradedFaces

namespace IsWellFormed

variable [DecidableEq α] {D} (hD : D.IsWellFormed)

include hD

end IsWellFormed

/-- The cells *below* the pair `X`: those whose graded index lies below `X`. -/
def below (X : Finset α × ℕ) : Set ι := {d | D.gradedIndex d ≤ X}

/-- The cells below a pair increase with the pair. -/
theorem below_mono : Monotone D.below := sorry

/-- The cells *visible* in `S`: those whose scope lies in `S`. -/
def visible (S : Set α) : Set ι := {d | (D.scope d : Set α) ⊆ S}

/-- The scheme whose cells are read through `φ : κ → ι`: the cell `t` has the scope and grade of
`φ t`; ground and faces are unchanged.  Along an equivalence this is a relabelling of cells;
along the inclusion of `D.below X` it is the scheme `D⟨X⟩` of cells below `X`. -/
def reindex (φ : κ → ι) : CellScheme κ α where
  ground := D.ground
  faces := D.faces
  scope := D.scope ∘ φ
  grade := D.grade ∘ φ

/-- Reindexing a well-formed scheme along any map from a finite type of cells gives a well-formed
scheme (cells may be duplicated). -/
theorem IsWellFormed.reindex [DecidableEq α] [Finite κ] {D : CellScheme ι α}
    (hD : D.IsWellFormed) (φ : κ → ι) : (D.reindex φ).IsWellFormed := sorry

section Restrict

variable [DecidableEq α]

end Restrict

section Comap

/-- The **pullback** of a scheme along an embedding `f : β ↪ α`: ground set and scopes are pulled
back, the faces are the sets whose image is a face, and the cells are those visible through `f`
(scope inside the range of `f`), with their grades. -/
noncomputable def comap (f : β ↪ α) : CellScheme (D.visible (Set.range f)) β where
  ground := D.ground.preimage f f.injective.injOn
  faces := D.faces.preimage (Finset.map f) (map_injective f).injOn
  scope d := (D.scope d).preimage f f.injective.injOn
  grade d := D.grade d

variable (f : β ↪ α)

/-- The pullback of a well-formed scheme along an embedding whose range meets the ground set in
a closed face is well formed. -/
theorem IsWellFormed.comap [DecidableEq α] [DecidableEq β] {D : CellScheme ι α}
    (hD : D.IsWellFormed)
    (hf : (D.ground.preimage f f.injective.injOn).map f ∈ D.faces) :
    (D.comap f).IsWellFormed := sorry

end Comap

/-- A cell scheme is **complete** [Kni26, §2.5]: every graded face is the graded
index of some cell. -/
def IsComplete (D : CellScheme ι α) : Prop :=
  ∀ X ∈ D.gradedFaces, ∃ d, D.gradedIndex d = X

/-- A scheme is complete after reindexing along a surjective map of cells. -/
theorem IsComplete.reindex {D : CellScheme ι α} (hD : D.IsComplete) {φ : κ → ι}
    (hφ : Function.Surjective φ) : (D.reindex φ).IsComplete := sorry

/-- The pullback of a complete scheme along an embedding is complete: the image
`Prod.map (Finset.map f) id X` of a graded face `X` of the pullback is a graded face, whose cell is
visible through the embedding. -/
theorem IsComplete.comap {D : CellScheme ι α} (hD : D.IsComplete) (f : β ↪ α) :
    (D.comap f).IsComplete := sorry

/-- A map of cells `φ : κ → ι` is a **lower embedding** of `E` into `D` if it is injective,
preserves grades, preserves and reflects the graded order, and every cell of `D` below the image
of a cell is itself in the image.  Apart from the grades, this says that `φ` is an initial segment
(`InitialSeg`) for the graded preorders on cells (`IsLowerEmbedding.toInitialSeg`).  Lower
embeddings identify each lower set `E.below (E.gradedIndex s)` with
`D.below (D.gradedIndex (φ s))`. -/
structure IsLowerEmbedding (E : CellScheme κ β) (D : CellScheme ι α) (φ : κ → ι) : Prop where
  /-- The cell map is injective. -/
  injective : Function.Injective φ
  /-- The cell map preserves grades. -/
  grade_eq (t : κ) : D.grade (φ t) = E.grade t
  /-- The cell map preserves and reflects the graded order. -/
  le_iff (s t : κ) : D.gradedIndex (φ s) ≤ D.gradedIndex (φ t) ↔ E.gradedIndex s ≤ E.gradedIndex t
  /-- Every cell below the image of a cell is in the image. -/
  mem_range (t : κ) (d : ι) : D.gradedIndex d ≤ D.gradedIndex (φ t) → d ∈ Set.range φ

namespace IsLowerEmbedding

variable {μ γ : Type*} {F : CellScheme μ γ} {φ : κ → ι} {ψ : μ → κ}

/-- The identity is a lower embedding of a scheme into itself. -/
protected theorem id (D : CellScheme ι α) : D.IsLowerEmbedding D id := sorry

/-- Lower embeddings compose. -/
theorem comp {D : CellScheme ι α} (hφ : E.IsLowerEmbedding D φ) (hψ : F.IsLowerEmbedding E ψ) :
    F.IsLowerEmbedding D (φ ∘ ψ) := sorry

/-- Reindexing along an equivalence is a lower embedding. -/
theorem reindex (D : CellScheme ι α) (e : κ ≃ ι) : (D.reindex e).IsLowerEmbedding D e := sorry

variable {D} in
/-- The inverse of an equivalence of cells that is a lower embedding is a lower embedding. -/
theorem symm {e : κ ≃ ι} (h : E.IsLowerEmbedding D e) : D.IsLowerEmbedding E e.symm := sorry

/-- The inclusion of the cells below a pair is a lower embedding of `D⟨X⟩` into `D`. -/
theorem subtypeVal_below (D : CellScheme ι α) (X : Finset α × ℕ) :
    (D.reindex ((↑) : D.below X → ι)).IsLowerEmbedding D (↑) := sorry

/-- For a lower embedding `φ` and a cell `s`, the induced map from the cells below `s` to the
cells below `φ s` is a lower embedding of the schemes of cells below them. -/
theorem below {D : CellScheme ι α} (hφ : E.IsLowerEmbedding D φ) (s : κ) :
    (E.reindex ((↑) : E.below (E.gradedIndex s) → κ)).IsLowerEmbedding
      (D.reindex ((↑) : D.below (D.gradedIndex (φ s)) → ι))
      (fun t ↦ ⟨φ t, (hφ.le_iff t s).mpr t.2⟩) := sorry

/-- The inclusion of the cells visible through an embedding is a lower embedding of the
pullback. -/
theorem comap (D : CellScheme ι α) (f : β ↪ α) :
    (D.comap f).IsLowerEmbedding D (↑) := sorry

section BelowEquiv

variable {D}

/-- For a lower embedding `φ` mapping the cells below `X` onto the cells below `Y`, the induced
equivalence of these lower sets. -/
noncomputable def belowEquiv {X : Finset β × ℕ} {Y : Finset α × ℕ} (hφ : E.IsLowerEmbedding D φ)
    (h : φ '' E.below X = D.below Y) : E.below X ≃ D.below Y :=
  Set.BijOn.equiv φ ⟨(Set.image_eq_iff_surjOn_mapsTo.mp h).2, hφ.injective.injOn,
    (Set.image_eq_iff_surjOn_mapsTo.mp h).1⟩

end BelowEquiv

end IsLowerEmbedding

/-- Cell schemes with finitely many cells over a countable ground type form a countable type. -/
instance countable [Finite ι] [Countable α] : Countable (CellScheme ι α) := sorry

end CellScheme

end VaughtConjecture
