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

namespace VaughtConjecture.Label

open Finset Ordinal

variable {k : ℕ} {x y z h : Label.{u}}

/-- The block index `o / ω` of an ordinal label `o` (zero at bottom and the formal top). -/
noncomputable def blockIndex (y : Label.{u}) : Ordinal.{u} :=
  WithTop.untopD 0 (WithBot.unbotD 0 y) / ω

/-- The **block move** to the block of `y`: an ordinal label `o` goes to the point of the block of
`y` with the finite part of `o`; bottom and the formal top are fixed. -/
noncomputable def moveToBlock (y : Label.{u}) : Label.{u} → Label.{u} :=
  WithBot.map (WithTop.map fun o ↦ ω * blockIndex y + o % ω)

variable {ι : Type*} {w w' a : ι → Label.{u}}

/-- The key of `x` is a **key** of `w` at grade `k`: some value of `w` other than bottom has the
key of `x`. -/
def IsKey (k : ℕ) (w : ι → Label.{u}) (x : Label.{u}) : Prop :=
  ∃ d, w d ≠ ⊥ ∧ visibilityReplace k k (w d) = visibilityReplace k k x

/-- The key of `x` is an **orbit key** of `w` at grade `k`: some value of `w` with the key of `x`
is not self-visible at `k`. -/
def IsOrbitKey (k : ℕ) (w : ι → Label.{u}) (x : Label.{u}) : Prop :=
  ∃ d, visibilityReplace k k (w d) = visibilityReplace k k x ∧ ¬ IsSelfVisible k (w d)

variable [Fintype ι]

/-- The **key rank** of `x` for `w` at grade `k`: the number of distinct keys `vr k k (w d)` of the
values of `w` other than bottom that are at most the key `vr k k x` of `x`. -/
noncomputable def keyRank (k : ℕ) (w : ι → Label.{u}) (x : Label.{u}) : ℕ :=
  valueRank (fun d ↦ visibilityReplace k k (w d)) (visibilityReplace k k x)

open Classical in
/-- The **code block** of `x` for `w` at grade `k`, with `r` the key rank of `x`: the block `0` of
the natural strip when the key of `x` is the orbit key `k`; the block `2 r` when it is any other
orbit key or not a key of `w`; and the block `2 r - 1` of the canonical point of rank `r` when it
is a key of `w` and not an orbit key. -/
noncomputable def codeBlock (k : ℕ) (w : ι → Label.{u}) (x : Label.{u}) : ℕ :=
  if IsOrbitKey k w x ∧ visibilityReplace k k x = gridPoint k 0 then 0
  else 2 * keyRank k w x - if IsKey k w x ∧ ¬ IsOrbitKey k w x then 1 else 0

open Classical in
/-- The **orbit map** of a labelling `w` at grade `k`: bottom is fixed; a label whose key is an
orbit key of `w` moves to its code block with its finite part (the block move); every other label
goes to the grid point `ω * b + k` of its code block `b`. -/
noncomputable def orbitMap (k : ℕ) (w : ι → Label.{u}) (x : Label.{u}) : Label.{u} :=
  if x = ⊥ then ⊥
  else if IsOrbitKey k w x then moveToBlock (gridPoint k (codeBlock k w x)) x
  else gridPoint k (codeBlock k w x)

/-- The **orbit code** of a labelling `w` at grade `k`: the orbit map applied to its values. -/
noncomputable def orbitCode (k : ℕ) (w : ι → Label.{u}) : ι → Label.{u} :=
  orbitMap k w ∘ w

/-- The **code grid** at grade `k` with block bound `B`: bottom and the points `ω * b + f` with
`b ≤ B` and `f ≤ k`.  It contains the grid of the same bound and the orbit codes. -/
noncomputable def codeGrid (k B : ℕ) : Finset Label.{u} :=
  insert ⊥ (((range (B + 1)) ×ˢ (range (k + 1))).image fun p ↦
    ((ω * (p.1 : Ordinal.{u}) + (p.2 : Ordinal.{u}) : Ordinal.{u}) : Label.{u}))

end VaughtConjecture.Label

namespace VaughtConjecture.CellScheme.Rows

open Label

variable {ι α : Type*} [Fintype ι] {D : CellScheme ι α} {R : D.Rows.{u}} {k : ℕ}

/-- **The orbit code of a labelling lawful below a pair is lawful below it**, when the cells
below the pair have grade at most `k`: the orbit map is a witness bounded by grade `k` that sends
only bottom to bottom. -/
theorem IsLawfulBelow.orbitCode {X : Finset α × ℕ} {w : ι → Label.{u}}
    (hw : R.IsLawfulBelow X fun d ↦ w d) (hk : ∀ d : D.below X, D.grade d ≤ k) :
    R.IsLawfulBelow X fun d ↦ Label.orbitCode k w d := sorry

end VaughtConjecture.CellScheme.Rows
