import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import dep.EconCSLib.Foundations.Probability.FiniteExpectation

open scoped BigOperators

namespace EconCSLib

noncomputable section

/-- Adjacent low indices in a finite chain. -/
abbrev FiniteAdjacentIndex (n : ℕ) :=
  {m : Fin n // m.val + 1 < n}

/-- The successor index associated with an adjacent finite-chain index. -/
def FiniteAdjacentIndex.succ {n : ℕ} (m : FiniteAdjacentIndex n) :
    Fin n :=
  ⟨m.1.val + 1, m.2⟩

/-- Adjacent low indices in the interval from `i` to `j`. -/
abbrev FiniteIntervalAdjacentIndex {n : ℕ} (i j : Fin n) :=
  {m : Fin n // i.val ≤ m.val ∧ m.val < j.val}

/-- The successor index associated with an interval-adjacent index. -/
def FiniteIntervalAdjacentIndex.succ {n : ℕ} {i j : Fin n}
    (m : FiniteIntervalAdjacentIndex i j) : Fin n :=
  ⟨m.1.val + 1, lt_of_le_of_lt (Nat.succ_le_of_lt m.2.2) j.isLt⟩

end

end EconCSLib
