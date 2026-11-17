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
public import dep.ArkLib.Data.Fin.Fold
public import dep.ArkLib.Data.Fin.Tuple.Defs
public import dep.ArkLib.Data.Fin.Tuple.Lemmas
public import dep.ArkLib.Data.Fin.Tuple.Notation
public import dep.CompPoly.Data.Classes.DCast

@[expose] public section

universe u v w

open Finset

namespace Fin

section BigOperators

variable {α : Type*}

/-- Version of multiplying over `Fin` vectors with good definitional equalities, using `dfoldl'`.

The definitional equality we want is that:
`vprod a = a 0 * (a 1 * (... * (a (n-1) * 1)))`
-/
@[to_additive vsum /-- Version of summing over `Fin` vectors with good definitional equalities,
using `dfoldl'`.

The definitional equality we want is that: `vsum a = a 0 + (a 1 + (... + (a (n-1) + 0)))`.

When `x + 0 = x` definitionally in `α`, we have the following definitional equalities:
- `vsum !v[] = 0`
- `vsum !v[a] = a`
- `vsum !v[a, b] = a + b`
- `vsum !v[a, b, c] = a + (b + c)`
- and so on
-/]
def vprod [CommMonoid α] {n : ℕ} (a : Fin n → α) : α :=
  Fin.dfoldr' n (fun _ => α) (fun i acc => a i * acc) 1

attribute [implicit_reducible] vprod vsum

variable {n : ℕ}

end BigOperators

end Fin

namespace Fin

section Sigma

variable {m : ℕ} {n : Fin m → ℕ}

/-- Embed nested indices `(i : Fin m, j : Fin (n i))` into a single index `Fin (vsum n)`. This
  converts from nested indexing to indexing into the vector sum, preserving lexicographic order. -/
@[implicit_reducible]
def embedSum {m : ℕ} {n : Fin m → ℕ} (i : Fin m) (j : Fin (n i)) : Fin (vsum n) := match m with
  | 0 => i
  | _ + 1 => match i with
    | 0 => Fin.castAdd _ j
    | ⟨i + 1, h⟩ => Fin.natAdd _ (embedSum ⟨i, Nat.succ_lt_succ_iff.mp h⟩ j)

end Sigma

end Fin

namespace Fin

variable {α : Sort*}

/-- Dependent flatten with unified motive: flattens a nested dependent vector
`(i : Fin m) → (j : Fin (n i)) → motive (embedSum i j)` into a single dependent vector
`(k : Fin (vsum n)) → motive k`, preserving element order.

This is meant to replace nested iteration for dependent families with a unified motive. -/
@[elab_as_elim, implicit_reducible]
def dflatten {m : ℕ} {n : Fin m → ℕ} {motive : (k : Fin (vsum n)) → Sort*}
    (v : (i : Fin m) → (j : Fin (n i)) → motive (embedSum i j)) (k : Fin (vsum n)) : motive k :=
  match m with
  | 0 => Fin.elim0 k
  | _ + 1 =>
    dappend
      (fun j => v 0 j)
      (fun j => dflatten (motive := fun j => motive (natAdd _ j)) (fun i => v i.succ) j)
      k

/-- Homogeneous flatten: flattens a nested homogeneous vector
`(i : Fin m) → (j : Fin (n i)) → α` into a single homogeneous vector `Fin (vsum n) → α`
by specializing `dflatten` to the constant-type motive `fun _ => α`. -/
def vflatten {m : ℕ} {n : Fin m → ℕ} (v : (i : Fin m) → Fin (n i) → α) :
    Fin (vsum n) → α :=
  dflatten v

/-- Functorial flatten with two arguments: flattens two nested heterogeneous tuple
`(i : Fin m) → (j : Fin (n i)) → F (α i j)` into a single heterogeneous tuple with type
`(k : Fin (vsum n)) → F (vflatten α k)` where `vflatten` operates on the vector of types `α`.

Unlike `dflatten` which requires an explicit unified motive, `fflatten` uses `vflatten` to
automatically construct the motive from the input type family. -/
def fflatten₂ {A : Sort u} {B : Sort v} {F : A → B → Sort w} {m : ℕ} {n : Fin m → ℕ}
    {α : (i : Fin m) → (j : Fin (n i)) → A} {β : (i : Fin m) → (j : Fin (n i)) → B}
    (v : (i : Fin m) → (j : Fin (n i)) → F (α i j) (β i j)) :
    (k : Fin (vsum n)) → F (Fin.vflatten α k) (Fin.vflatten β k) :=
  match m with
  | 0 => !h[]
  | _ + 1 => fappend₂ (v 0) (fflatten₂ (fun i => v i.succ))

section FinSigmaFinEquiv

variable {n : ℕ}

def map {α β : Fin n → Sort*} (f : (i : Fin n) → α i → β i) (a : (i : Fin n) → α i) :
    (i : Fin n) → β i := fun i => f i (a i)

def range (n : ℕ) : Fin n → ℕ := fun i => i

end FinSigmaFinEquiv

end Fin
