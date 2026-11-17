import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.InitialSeg
import Mathlib.Order.SupClosed
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Ordinal.Arithmetic
import dep.Extension.Basic
import dep.Extension.Gate
import dep.Extension.GatedExtension
import dep.Geometry.ConvexGeometry
import dep.Geometry.Plan
import dep.Label.Basic
import dep.Label.Cap
import dep.Label.OrdinalVisibility
import dep.Label.Transform
import dep.Label.Visibility
import dep.Realization.Basic
import dep.Realization.Families
import dep.Realization.Hull
import dep.Realization.Model
import dep.Realization.Transport
import dep.Scheme.Bountiful
import dep.Scheme.Cell
import dep.Scheme.Row
import dep.Scheme.Transport
import dep.Stage.Basic
import dep.Stage.Countable
import dep.Stage.Legal
import dep.Stage.Scheme
import dep.Stage.TopFree

universe u v

namespace VaughtConjecture

open Finset Label

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}

/-- **Finite-cut receiving for models, conditional on the coupled gated pinned extension
property**: a model at a stage `α` at which `StageType.HasCoupledGatedPinnedExtensions α` holds
has the finite-cut receiving property.  This is (R1) of the table of Layer 3 conditional on that
named hypothesis, which is open; it is not a proof of (R1).

The private context at the floor of the cutoff (`IsModel.exists_privateContext_isAnchored`) and
the coupled gated extension given by the hypothesis are realized over the private tuple by
generalized saturation, whose instance is witnessed nonempty by the display itself; gate recovery
with the twin–gate coupling
(`StageType.CoupledGatedExtension.exists_restrictFace_mem_receivingFamily`) gives the donor face,
in the receiving family of the donor at the label of the cap, hence at the cutoff.  Of the clauses
of a model, uniformity, high-arity dominance, legality of types, exact consistency, and
generalized saturation are used; no hypothesis on the stage is.  Different cutoffs may use
different occurrences; nothing is claimed about uniqueness, coherence, or exact receiving. -/
theorem IsModel.hasFiniteCutReceiving_of_hasCoupledGatedPinnedExtensions (hR : R.IsModel)
    (hg : StageType.HasCoupledGatedPinnedExtensions α) : R.HasFiniteCutReceiving := sorry

end Realization

end VaughtConjecture
