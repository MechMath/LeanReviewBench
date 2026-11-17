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
public import dep.ArkLib.Data.Classes.Slice
public import dep.ArkLib.Data.Fin.Basic
public import dep.ArkLib.Data.Fin.Tuple.Defs
public import dep.ArkLib.Data.Fin.Tuple.Notation
public import dep.CompPoly.Data.Classes.DCast

@[expose] public section

universe u v w

namespace Fin

variable {m n : ℕ} {α : Sort u}

instance : Unique (Fin 0 → α) where
  uniq v := sorry

instance {α : Fin 0 → Sort u} : Unique ((i : Fin 0) → α i) where
  uniq := fun v => sorry

/-- `dcons` is equal to `cons`. Marked as `csimp` to allow for switching to the `cons`
  implementation during execution. -/
@[csimp]
theorem dcons_eq_cons : @dcons = @cons := sorry

/-- `dconcat` is equal to `snoc`. Marked as `csimp` to allow for switching to the `snoc`
  implementation during execution. -/
@[csimp]
theorem dconcat_eq_snoc : @dconcat = @snoc := sorry

/-- `dappend` is equal to `addCases`. Marked as `csimp` to allow for switching to the `addCases`
  implementation during execution. -/
@[csimp]
theorem dappend_eq_addCases : @dappend = @addCases := sorry

/-- `vappend` is equal to `append`. Marked as `csimp` to allow for switching to the `append`
  implementation during execution. -/
@[csimp]
theorem vappend_eq_append : @vappend = @append := sorry

lemma vappend_left_of_lt {m n : ℕ} {α : Sort u}
    (u : Fin m → α) (v : Fin n → α) (i : Fin (m + n)) (h : i.val < m) :
      vappend u v i = u ⟨i, h⟩ := sorry

lemma vappend_right_of_not_lt {m n : ℕ} {α : Sort u}
    (u : Fin m → α) (v : Fin n → α) (i : Fin (m + n)) (h : ¬ i.val < m) :
      vappend u v i = v ⟨i - m, by omega⟩ := sorry

section FunctorialBinary

variable {A : Sort u} {B : Sort v} {F₂ : A → B → Sort w} {m n : ℕ}

end FunctorialBinary

section FunctorialUnary

variable {A : Sort u} {F : A → Sort v} {m n : ℕ} {α : A}

end FunctorialUnary

instance {α : Fin 0 → Sort u} : Unique ((i : Fin 0) → α i) where
  default := fun i => elim0 i
  uniq v := sorry

variable {m n : ℕ} {α : Sort u}

section padding

end padding

end Fin
