import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.Data.Finset.Union
import Mathlib.Data.Set.Countable
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

namespace FreshGenerator

open FreeGroup

universe u

variable {α : Type u} [DecidableEq α] [Infinite α]

instance [Countable α] : Countable (FreeGroup α) := sorry

instance [Nonempty α] : Infinite (FreeGroup α) := sorry

noncomputable section

end

end FreshGenerator
