import Mathlib.Data.Countable.Defs
import Mathlib.Data.Sum.Basic
import Mathlib.SetTheory.Cardinal.Arithmetic

namespace AdjoinFresh

universe u

variable {α : Type u} [Countable α]

private noncomputable def e : ℕ ≃ ℕ ⊕ α := Classical.choice (inferInstance : Nonempty (ℕ ≃ ℕ ⊕ α))
