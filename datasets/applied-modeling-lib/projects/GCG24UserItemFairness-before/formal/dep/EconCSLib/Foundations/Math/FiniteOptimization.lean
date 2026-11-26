import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Order.Compact

namespace EconCSLib

noncomputable section

/-- Finite maximum of a real-valued function on a nonempty finite type. -/
def finiteMax {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) : ℝ :=
  (Finset.univ : Finset α).sup' Finset.univ_nonempty f

/-- Finite minimum of a real-valued function on a nonempty finite type. -/
def finiteMin {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) : ℝ :=
  (Finset.univ : Finset α).inf' Finset.univ_nonempty f

end

end EconCSLib
