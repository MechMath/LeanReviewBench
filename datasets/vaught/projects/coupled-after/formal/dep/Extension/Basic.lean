import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Fintype.Basic

open Finset

namespace VaughtConjecture

variable {m n k : ℕ}

/-- The face `f` followed by the new point: the embedding of `Fin (m + 1)` into `Fin (n + 1)`
that is `f` on `Fin m` and sends the last point to the last point. -/
def extendByLast (f : Fin m ↪ Fin n) : Fin (m + 1) ↪ Fin (n + 1) :=
  Fin.Embedding.snoc (f.trans Fin.castSuccEmb) (a := Fin.last n) fun ⟨i, hi⟩ ↦
    (Fin.castSucc_lt_last (f i)).ne hi

end VaughtConjecture
