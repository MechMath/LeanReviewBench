import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Prod.Lex
import Mathlib.Order.Interval.Finset.Fin

namespace VaughtConjecture

open Finset

variable {ca cb r : ℕ}

/-- The **merge** of two finite chains `Fin ca` and `Fin cb` along common subchains `ea` and `eb`:
the points of the first chain and the points of the second chain outside its common subchain. -/
inductive Merge (ea : Fin r ↪o Fin ca) (eb : Fin r ↪o Fin cb) : Type
  /-- A point of the first chain. -/
  | inl (i : Fin ca)
  /-- A point of the second chain outside its common subchain. -/
  | inr (j : Fin cb) (hj : j ∉ Set.range eb)
  deriving DecidableEq

namespace Merge

variable (ea : Fin r ↪o Fin ca) (eb : Fin r ↪o Fin cb)

/-- The merge as a sum type. -/
def equivSum : Merge ea eb ≃ Fin ca ⊕ {j : Fin cb // j ∉ Set.range eb} where
  toFun
    | inl i => .inl i
    | inr j hj => .inr ⟨j, hj⟩
  invFun
    | .inl i => inl i
    | .inr j => inr j.1 j.2
  left_inv x := sorry
  right_inv x := sorry

/-- The merge is finite: it is a sum of two finite types. -/
noncomputable instance : Fintype (Merge ea eb) := by
  classical
  exact Fintype.ofEquiv _ (equivSum ea eb).symm

/-- The number of points of the common subchain at most a point of the first chain. -/
def countLeft (i : Fin ca) : ℕ := #{t | ea t ≤ i}

/-- The number of points of the common subchain below a point of the second chain. -/
def countRight (j : Fin cb) : ℕ := #{t | eb t < j}

/-- The key of a point of the merge: the number of common points before it, then the chain it
comes from, then its position in that chain. -/
def key : Merge ea eb → ℕ ×ₗ ℕ ×ₗ ℕ
  | inl i => toLex (countLeft ea i, toLex (0, (i : ℕ)))
  | inr j _ => toLex (countRight eb j, toLex (1, (j : ℕ)))

/-- Distinct points of the merge have distinct keys. -/
theorem key_injective : Function.Injective (key ea eb) := sorry

/-- The merge is ordered by the key. -/
instance : LinearOrder (Merge ea eb) := LinearOrder.lift' (key ea eb) (key_injective ea eb)

variable {ea eb}

variable (ea eb)

/-- The first chain in the merge. -/
def left : Fin ca ↪o Merge ea eb :=
  OrderEmbedding.ofStrictMono inl fun i i' h ↦ sorry

open Classical in
/-- The second chain in the merge: a point of the common subchain is sent to the corresponding
point of the first chain. -/
noncomputable def rightFun (j : Fin cb) : Merge ea eb :=
  if h : j ∈ Set.range eb then inl (ea (Classical.choose (Set.mem_range.mp h))) else inr j h

/-- The second chain is sent into the merge in increasing order. -/
theorem strictMono_rightFun : StrictMono (rightFun ea eb) := sorry

/-- The second chain in the merge, as an order embedding. -/
noncomputable def right : Fin cb ↪o Merge ea eb :=
  OrderEmbedding.ofStrictMono (rightFun ea eb) (strictMono_rightFun ea eb)

/-- The merge has `ca + (cb - r)` points. -/
theorem card : Fintype.card (Merge ea eb) = ca + (cb - r) := sorry

end Merge

end VaughtConjecture
