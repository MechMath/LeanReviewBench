module

public import Batteries.Data.Fin.Fold
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Take
public import Mathlib.Tactic.DepRewrite
public import Mathlib.Tactic.FinCases
public import dep.CompPoly.Data.Classes.DCast

@[expose] public section

universe u v w

set_option backward.isDefEq.respectTransparency false

namespace Fin

open Function

section Append

variable {m n : ℕ} {α β : Sort*}

@[simp]
lemma append_zero_of_succ_left {u : Fin (m + 1) → α} {v : Fin n → α} :
    (append u v) 0 = u 0 := sorry

end Append

section Sum

end Sum

section OptionEquivPrime

variable {n : ℕ}

end OptionEquivPrime

end Fin
