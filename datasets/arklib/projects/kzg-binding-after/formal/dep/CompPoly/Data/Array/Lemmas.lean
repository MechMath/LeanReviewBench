module

public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Cases

@[expose] public section

universe u

namespace Array

variable {α : Type*} {unit : α}

/-- `Array` version of `List.matchSize`, which rightpads the arrays to the same length. -/
@[reducible]
def matchSize (a b : Array α) (unit : α) : Array α × Array α :=
  (a.rightpad (b.size) unit, b.rightpad (a.size) unit)

attribute [simp] Array.getElem?_eq_getElem

/-- find index from the end of an array -/
def findIdxRev? (cond : α → Bool) (as : Array α) : Option (Fin as.size) :=
  find ⟨ as.size, Nat.lt_succ_self _ ⟩
where
  find : Fin (as.size + 1) → Option (Fin as.size)
    | 0 => none
    | ⟨ i+1, h ⟩ =>
      if (cond as[i]) then
        some ⟨ i, Nat.lt_of_succ_lt_succ h ⟩
      else
        find ⟨ i, Nat.lt_of_succ_lt h ⟩

/-- Get the last element of an array, assuming the array is non-empty. -/
def getLast (a : Array α) (h : a.size > 0) : α := a[a.size - 1]

/-- Get the last element of an array, or `v₀` if the array is empty. -/
def getLastD (a : Array α) (v₀ : α) : α := a.getD (a.size - 1) v₀

end Array
