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

def generatorNames' : List (α × Bool) → Finset α
  | [] => ∅
  | ((x,_) :: l) => {x} ∪ generatorNames' l

def generatorNames (x : FreeGroup α) : Finset α := generatorNames' $ FreeGroup.toWord x

theorem existsFreshGeneratorName (A : Finset (FreeGroup α)) :
    ∃ a, a ∉ A.biUnion generatorNames := sorry

noncomputable def freshGeneratorName (A : Finset (FreeGroup α)) : α :=
  (existsFreshGeneratorName A).choose

noncomputable def freshGenerator (A : Finset (FreeGroup α)) : FreeGroup α :=
  FreeGroup.of (freshGeneratorName A)

def dropGenerators (S : Finset α) : FreeGroup α →* FreeGroup α := lift (fun i => if i ∈ S then 1 else of i)

def forgetOld (S : Finset (FreeGroup α)) : FreeGroup α →* FreeGroup α := dropGenerators (S.biUnion generatorNames)

omit [Infinite α] in
@[simp]
theorem forgetOld_old {S : Finset (FreeGroup α)} {x : FreeGroup α} (hxS : x ∈ S) : forgetOld S x = 1 := sorry

noncomputable section

end

end FreshGenerator
