import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Countable
import Mathlib.Order.InitialSeg
import Mathlib.Order.SupClosed
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Ordinal.Arithmetic
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

variable {α β γ : Ordinal.{u}} {n m : ℕ}

/-- The **cofaces** of a stage type `p` on `n` points [Kni26, Definition 3.2.1]: the legal stage
types on `n + 1` points whose face along the initial segment is `p`. -/
def cofaces (p : StageType.{u} α n) : Set (StageType.{u} α (n + 1)) :=
  {q | q.IsLegal ∧ restrictFace Fin.castSuccEmb q = some p}

/-- **Generalized saturation** [Kni26, Definition 3.2.1, clause 4(a)i]: the stage types on
`n + 1` points with scheme `S`. -/
def saturationFamily (S : Scheme.{u} (n + 1)) : Set (StageType.{u} α (n + 1)) :=
  {q | q.toScheme = S}

/-- The **bottom pattern** [Kni26, Definition 3.2.1, clause 4(a)ii]: the stage types on `n + 1`
points with scheme `S` whose labels on the cells of grade at most `n` are bottom exactly where
the labelling `ρ` of the cells of `S` is bottom. -/
def bottomPatternFamily (S : Scheme.{u} (n + 1)) (ρ : Fin S.card → Label.{u}) :
    Set (StageType.{u} α (n + 1)) :=
  {q | q.toScheme = S ∧ ∀ (i : Fin q.card) (j : Fin S.card), (i : ℕ) = j →
    q.toCellScheme.grade i ≤ n → (q.label i = ⊥ ↔ ρ j = ⊥)}

/-- **Uniformity** [Kni26, Definition 3.2.1, clause 4(b)]: the stage types on `n + 1` points with
a label in `[γ, γ + ω)`.  The clause of a model uses it for every `γ` that is zero or a limit and
below the stage, where the interval is a block. -/
def uniformityFamily (γ : Ordinal.{u}) : Set (StageType.{u} α (n + 1)) :=
  {q | ∃ d, (γ : Label.{u}) ≤ q.label d ∧ q.label d < ((γ + Ordinal.omega0 : Ordinal.{u}) : Label)}

/-- **High-arity dominance** [Kni26, Definition 3.2.1, clause 4(c)]: the stage types on `n + 1`
points with a label above `γ` at a cell of grade `n + 1`.  The clause of a model uses it for
`γ` below the stage. -/
def dominanceFamily (γ : Ordinal.{u}) : Set (StageType.{u} α (n + 1)) :=
  {q | ∃ d, q.toCellScheme.grade d = n + 1 ∧ (γ : Label.{u}) < q.label d}

variable {p : StageType.{u} α n} {q : StageType.{u} α (n + 1)} {S : Scheme.{u} (n + 1)}
  {ρ : Fin S.card → Label.{u}}

/-- The **receiving family** of a stage type `d` at a cutoff `c`: the stage types on the scheme of
`d` with the observation of `d` at `c`. -/
def receivingFamily (d : StageType.{u} α n) (c : Label.{u}) : Set (StageType.{u} α n) :=
  {q | q.toScheme = d.toScheme ∧
    ∀ (i : Fin q.card) (j : Fin d.card), (i : ℕ) = j → min (q.label i) c = min (d.label j) c}

section Repair

end Repair

section Reindex

variable (e : Fin (n + 1) ≃ Fin (n + 1))

end Reindex

section Reduce

variable (hβ : Order.IsSuccPrelimit β)

end Reduce

section ReduceBackwards

end ReduceBackwards

section Nonempty

variable {S : Scheme.{u} (n + 1)} {p : StageType.{u} α n}

end Nonempty

section Lift

end Lift

end StageType

end VaughtConjecture
