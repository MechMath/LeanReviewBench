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
import dep.Realization.Basic
import dep.Scheme.Cell
import dep.Scheme.Row
import dep.Stage.Basic
import dep.Stage.Scheme

universe u v w x

namespace VaughtConjecture.Realization

open Finset

variable {α β γ : Ordinal.{u}} {M : Type v} {N : Type w} {P : Type x} {m n : ℕ}
  {R : Realization.{u, v} α M}

section Map

variable (e : M ≃ N) (R)

/-- The **transport** of a realization along a bijection of carriers: a tuple of `N` has the type
of its preimage in `M`. -/
def map : Realization.{u, w} α N where
  eval t := R.eval (t.trans e.symm.toEmbedding)

variable {R e}

/-- Exact consistency is preserved by transport. -/
theorem IsConsistent.map (hR : R.IsConsistent) (e : M ≃ N) : (R.map e).IsConsistent := sorry

/-- Covering is preserved by transport. -/
theorem IsCovering.map (hc : R.IsCovering) (e : M ≃ N) : (R.map e).IsCovering := sorry

variable (e) in
/-- The **transport** of an occurrence: the image tuple with the same type. -/
def Occurrence.map (x : R.Occurrence) : (R.map e).Occurrence where
  arity := x.arity
  tuple := x.tuple.trans e.toEmbedding
  type := x.type
  eval_tuple := sorry

/-- The occurrence of `R` underlying an occurrence of the transport: the preimage tuple with the
same type. -/
def Occurrence.comap (e : M ≃ N) (y : (R.map e).Occurrence) : R.Occurrence where
  arity := y.arity
  tuple := y.tuple.trans e.symm.toEmbedding
  type := y.type
  eval_tuple := y.eval_tuple

end Map

section Reduce

variable (R)

variable {R}

end Reduce

end VaughtConjecture.Realization
