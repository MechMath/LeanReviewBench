module

public import Mathlib.Data.Fin.Tuple.Take

@[expose] public section

universe u v w

namespace Fin

/-- Extract a sub-tuple from a `Fin`-tuple, from index `start` to `stop - 1`. -/
def extract {n : ℕ} {α : Fin n → Sort*} (start stop : ℕ) (h1 : start ≤ stop) (h2 : stop ≤ n)
    (v : (i : Fin n) → α i) : (i : Fin (stop - start)) → α ⟨i + start, sorry⟩ :=
  fun i ↦ v ⟨i + start, sorry⟩

/-- Pad a `Fin`-indexed vector on the right with an element `a`.

This becomes truncation if `n < m`. -/
def rightpad {m : ℕ} {α : Sort*} (n : ℕ) (a : α) (v : Fin m → α) : Fin n → α :=
  fun i => if h : i < m then v ⟨i, h⟩ else a

section Vec

variable {α : Sort*}

end Vec

/-- Cast a dependent or heterogeneous vector across an equality `n' = n` and a family of equalities
  `∀ i, α (Fin.cast h i) = α' i`.

This is meant to replace `Fin.cast` for our use cases, as this definition offers better
definitional equality. -/
protected def dcast {n n' : ℕ} {α : Fin n → Sort u} {α' : Fin n' → Sort u}
    (h : n' = n) (hα : ∀ i, α (Fin.cast h i) = α' i) (v : (i : Fin n) → α i) :
      (i : Fin n') → α' i :=
  fun i => _root_.cast (hα i) (v (Fin.cast h i))

end Fin
