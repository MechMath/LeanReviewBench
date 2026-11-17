import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
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
import dep.Extension.Gate
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

namespace StageType

variable {α : Ordinal.{u}} {n m : ℕ}

/-- A **gated extension** of a stage type `P` on `n` points over the face `f`, with donor
`d` on `m + 1` points: a legal **display** on `n + 1` points whose faces along `Fin.castSuccEmb`
and `extendByLast f` are literally `P` and `d`, with a **gate** of graded index `(univ, n)` whose
twins are labelled `⊥` and whose row reads the new donor cells against the **cap**, of graded index
`(univ.map Fin.castSuccEmb, n)`. -/
structure GatedExtension (P : StageType.{u} α n) (f : Fin m ↪ Fin n)
    (d : StageType.{u} α (m + 1)) where
  /-- The display. -/
  display : StageType.{u} α (n + 1)
  /-- The display is legal. -/
  isLegal : display.IsLegal
  /-- The private face of the display is literally `P`. -/
  restrictFace_castSuccEmb : restrictFace Fin.castSuccEmb display = some P
  /-- The donor face of the display is literally `d`. -/
  restrictFace_extendByLast : restrictFace (extendByLast f) display = some d
  /-- The gate. -/
  gate : Fin display.card
  /-- The cap, the private cap seen in the display. -/
  cap : Fin display.card
  /-- The gate has full scope and grade `n`. -/
  gradedIndex_gate : display.toCellScheme.gradedIndex gate = (univ, n)
  /-- The cap has full scope on the private points and grade `n`. -/
  gradedIndex_cap : display.toCellScheme.gradedIndex cap = (univ.map Fin.castSuccEmb, n)
  /-- The twins of the gate are labelled `⊥` in the display. -/
  label_twin : ∀ t, display.toCellScheme.gradedIndex t = (univ, n) → t ≠ gate →
    display.label t = ⊥
  /-- The gate data: the row of the gate reads every new donor cell. -/
  isGate : display.rows.IsGate gate cap (display.toCellScheme.visible (Set.range Fin.castSuccEmb))
    (display.toCellScheme.visible (Set.range (extendByLast f))) display.label

/-- The donor `d` is **anchored** in `P` below the cell `C`: every new donor cell whose label is
neither `⊥` nor at least that of `C` is labelled `vr_n(P.label z, i)` for an anchor `z` of `P`
and some `i ≤ n`. -/
def IsAnchored (P : StageType.{u} α n) (C : Fin P.card) (d : StageType.{u} α (m + 1)) : Prop :=
  ∀ j : Fin d.card, Fin.last m ∈ d.toCellScheme.scope j → d.label j ≠ ⊥ → d.label j < P.label C →
    ∃ z : Fin P.card, ∃ i ≤ n, d.label j = visibilityReplace n i (P.label z)

namespace GatedExtension

variable {P : StageType.{u} α n} {f : Fin m ↪ Fin n} {d : StageType.{u} α (m + 1)}
  (E : GatedExtension P f d)

end GatedExtension

/-- A **coupled gated extension** of a stage type `P` on `n` points over the face `f`, with donor
`d` on `m + 1` points: a gated extension (`GatedExtension`) in which the twins of the gate are not
required to be labelled `⊥`; instead the rows of the display couple them to the gate: every twin
reads the gate at least as it reads the cap (`CellScheme.Rows.TwinsReadGate`). -/
structure CoupledGatedExtension (P : StageType.{u} α n) (f : Fin m ↪ Fin n)
    (d : StageType.{u} α (m + 1)) where
  /-- The display. -/
  display : StageType.{u} α (n + 1)
  /-- The display is legal. -/
  isLegal : display.IsLegal
  /-- The private face of the display is literally `P`. -/
  restrictFace_castSuccEmb : restrictFace Fin.castSuccEmb display = some P
  /-- The donor face of the display is literally `d`. -/
  restrictFace_extendByLast : restrictFace (extendByLast f) display = some d
  /-- The gate. -/
  gate : Fin display.card
  /-- The cap, the private cap seen in the display. -/
  cap : Fin display.card
  /-- The gate has full scope and grade `n`. -/
  gradedIndex_gate : display.toCellScheme.gradedIndex gate = (univ, n)
  /-- The cap has full scope on the private points and grade `n`. -/
  gradedIndex_cap : display.toCellScheme.gradedIndex cap = (univ.map Fin.castSuccEmb, n)
  /-- The twins of the gate read the gate at least as the cap. -/
  twinsReadGate : display.rows.TwinsReadGate gate cap
  /-- The gate data: the row of the gate reads every new donor cell. -/
  isGate : display.rows.IsGate gate cap (display.toCellScheme.visible (Set.range Fin.castSuccEmb))
    (display.toCellScheme.visible (Set.range (extendByLast f))) display.label

variable (α) in
/-- The **coupled gated pinned extension property** at stage `α`: the gated pinned extension
property (`HasGatedPinnedExtensions`) with coupled gated extensions in place of gated extensions.
For every legal `P` on `n` points, every face `f` of `P` with restriction `p`, every legal
one-point coface `d` of `p`, and every cell `C` of `P` of graded index `(univ, n)` not labelled
`⊥` below which `d` is anchored, if `m + 1 < n` there is a coupled gated extension of `P` over `f`
with donor `d` whose cap carries the label of `C`.

This is a **named hypothesis, and it is open**.  It is proved at one input only: the input at
which `HasGatedPinnedExtensions` is refuted, the private type `GatedExtensionCounterexample.P α`
over the empty root with the donor `P α|{0}` and the cap `3`
(`CoupledGateExamples.exists_coupledGatedExtension_comap_g₁`).  The open point is **cap
lowering (CL)**.  In every lawful labelling of the display the gate dominates the cap, so a lift
from a coatom `(F ∪ {y}, n)` (`F` a face of `n - 1` private points containing the root, `y` the new
point) whose prescriptions at a donor cell and at its anchor force the gate below a label `v`
also forces the private cap below `v`.  The statement to be decided is: for the private type `P`,
a face `F` of `n - 1` points, a cap `c` self-visible at `n`, a labelling `p` lawful below
`(F, n - 1)` in the cap ball of the labelling of `P` at `c`, and a label `v ≥ c` self-visible at
`n`, some lawful labelling of `P` extends `p`, lies in that cap ball, and is at most `v` at `C`.
(CL) is the uniform form of that requirement, over every `p` and every `v ≥ c`; it is a
strengthening, not shown necessary for the property and not shown sufficient for it.  A failure
of (CL) refutes the coupled design only at a pair `(p, v)` that a forcing prescription from an
anchored legal donor actually realizes.  The case of a donor labelled `⊤` on `P α`, which
exercises it, is not compiled. -/
def HasCoupledGatedPinnedExtensions : Prop :=
  ∀ {n m : ℕ} (P : StageType.{u} α n) (f : Fin m ↪ Fin n) (p : StageType.{u} α m)
    (d : StageType.{u} α (m + 1)) (C : Fin P.card),
    P.IsLegal → restrictFace f P = some p → d.IsLegal → restrictFace Fin.castSuccEmb d = some p →
    P.toCellScheme.gradedIndex C = (univ, n) → P.label C ≠ ⊥ → m + 1 < n → IsAnchored P C d →
    ∃ E : CoupledGatedExtension P f d, E.display.label E.cap = P.label C

namespace CoupledGatedExtension

variable {P : StageType.{u} α n} {f : Fin m ↪ Fin n} {d : StageType.{u} α (m + 1)}
  (E : CoupledGatedExtension P f d)

end CoupledGatedExtension

end StageType

end VaughtConjecture
