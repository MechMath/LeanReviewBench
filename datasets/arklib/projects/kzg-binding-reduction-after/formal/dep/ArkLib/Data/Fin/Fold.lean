module

public import Batteries.Data.Fin.Fold
public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic.DepRewrite
public import dep.CompPoly.Data.Classes.DCast

@[expose] public section

universe u v

namespace Fin

variable {m : Type u → Type v} [Monad m]

/-- Heterogeneous left fold over `Fin n` in a monad, prime version with better defeq.
  Automatically unfolds for `0` and `n.succ`. -/
@[implicit_reducible]
def dfoldlM' (n : ℕ) (α : Fin (n + 1) → Type u)
    (f : (i : Fin n) → α i.castSucc → m (α i.succ)) (init : α 0) : m (α (last n)) :=
  match n with
  | 0 => pure init
  | n + 1 => do
    let x ← dfoldlM' n (α ∘ castSucc) (fun i => f i.castSucc) init
    f (last n) x

/-- Heterogeneous left fold over `Fin n`, prime version with better defeq.
  Automatically unfolds for `0` and `n.succ`. -/
@[implicit_reducible]
def dfoldl' (n : ℕ) (α : Fin (n + 1) → Type u)
    (f : (i : Fin n) → α i.castSucc → α i.succ) (init : α 0) : α (last n) :=
  dfoldlM' (m := Id) n α f init

/-- Compiler replacement rule: use `dfoldl'` instead of `dfoldl` for better defeq. -/
@[csimp] lemma dfoldl_eq_dfoldl' : @dfoldl = @dfoldl' := sorry

/-- Heterogeneous right fold over `Fin n` in a monad, prime version with better defeq.
  Automatically unfolds for `0` and `n.succ`. -/
@[implicit_reducible]
def dfoldrM' {m : Type u → Type v} [Monad m]
    (n : ℕ) (α : Fin (n + 1) → Type u)
    (f : (i : Fin n) → α i.succ → m (α i.castSucc)) (init : α (last n)) : m (α 0) :=
  match n with
  | 0 => pure init
  | n + 1 => do
    let x ← dfoldrM' n (α ∘ succ) (fun i => f i.succ) init
    f 0 x

/-- Heterogeneous right fold over `Fin n`, prime version with better defeq.
  Automatically unfolds for `0` and `n.succ`. -/
@[implicit_reducible]
def dfoldr' (n : ℕ) (α : Fin (n + 1) → Type u)
    (f : (i : Fin n) → α i.succ → α i.castSucc) (init : α (last n)) : α 0 :=
  dfoldrM' (m := Id) n α f init

/-- Compiler replacement rule: use `dfoldr'` instead of `dfoldr` for better defeq. -/
@[csimp] lemma dfoldr_eq_dfoldr' : @dfoldr = @dfoldr' := sorry

section Examples

end Examples

section FoldCongr

end FoldCongr

end Fin
