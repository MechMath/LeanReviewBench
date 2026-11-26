import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Countable
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.InitialSeg
import Mathlib.Order.SupClosed
import Mathlib.SetTheory.Ordinal.Arithmetic
import dep.Geometry.ConvexGeometry
import dep.Geometry.Plan
import dep.Label.Basic
import dep.Label.OrdinalVisibility
import dep.Label.Transform
import dep.Label.Visibility
import dep.Scheme.Cell
import dep.Scheme.Row
import dep.Stage.Basic
import dep.Stage.Scheme

universe u v

namespace VaughtConjecture

open Finset

/-- A **realization** at stage `α` on the carrier `M`: an optional stage type for every injective
finite tuple.  This is raw data; the laws are `Realization.IsConsistent` and
`Realization.IsCovering`. -/
structure Realization (α : Ordinal.{u}) (M : Type v) where
  /-- The partial evaluation: the type of an injective tuple, if it has one. -/
  eval {n : ℕ} : (Fin n ↪ M) → Option (StageType.{u} α n)

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} {m n k : ℕ} (R : Realization.{u, v} α M)

/-- **Extensionality** for realizations: equal evaluations at every tuple. -/
@[ext] theorem ext {R R' : Realization.{u, v} α M}
    (h : ∀ {n : ℕ} (t : Fin n ↪ M), R.eval t = R'.eval t) : R = R' := sorry

/-- **Exact consistency** [Kni26, §3.2]: every face of a typed tuple has exactly the partial
restriction of its type, including `none` at an invisible face.  Nothing is required of the faces
of an untyped tuple. -/
def IsConsistent : Prop :=
  ∀ ⦃m n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n) (f : Fin m ↪ Fin n),
    R.eval t = some p → R.eval (f.trans t) = StageType.restrictFace f p

/-- **Covering** [Kni26, §3.2]: every injective finite tuple is a face of a typed tuple. -/
def IsCovering : Prop :=
  ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M),
    ∃ (m : ℕ) (u : Fin m ↪ M) (f : Fin n ↪ Fin m), f.trans u = t ∧ (R.eval u).isSome

/-- An **occurrence** in a realization: a typed tuple with its type. -/
structure Occurrence where
  /-- The number of points. -/
  arity : ℕ
  /-- The literal tuple. -/
  tuple : Fin arity ↪ M
  /-- The evaluated type. -/
  type : StageType.{u} α arity
  /-- The type is the evaluation of the tuple. -/
  eval_tuple : R.eval tuple = some type

attribute [simp] Occurrence.eval_tuple

variable {R}

namespace Occurrence

section LiteralFace

variable (hR : R.IsConsistent) {x y : R.Occurrence} {f : Fin x.arity ↪ Fin y.arity}

include hR

end LiteralFace

end Occurrence

/-- **Reindexing a typed tuple**: along a bijection `e` of coordinates, the reindexed tuple has
the reindexed type. -/
theorem eval_equiv_trans_of_eval (hR : R.IsConsistent) {t : Fin n ↪ M} {p : StageType.{u} α n}
    (ht : R.eval t = some p) (e : Fin m ≃ Fin n) :
    R.eval (e.toEmbedding.trans t) = some (p.reindex e) := sorry

/-- The **reindexing** of an occurrence along a bijection of coordinates. -/
noncomputable def Occurrence.reindex (hR : R.IsConsistent) (x : R.Occurrence)
    (e : Fin m ≃ Fin x.arity) : R.Occurrence where
  arity := m
  tuple := e.toEmbedding.trans x.tuple
  type := x.type.reindex e
  eval_tuple := eval_equiv_trans_of_eval hR x.eval_tuple e

end Realization

end VaughtConjecture
