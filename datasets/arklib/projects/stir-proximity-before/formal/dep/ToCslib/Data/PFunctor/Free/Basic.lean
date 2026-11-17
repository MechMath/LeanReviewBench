module

public import Cslib.Foundations.Data.PFunctor.Free
public import dep.dep.CslibCompat.Free

public section

universe u v w uA uB

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {α β : Type*}

/-- Mapping twice composes the leaf functions, including across independent universes. -/
theorem map_map {γ : Type*} (f : β → γ) (g : α → β) (program : P.FreeM α) :
    map f (map g program) = map (f ∘ g) program := sorry

end PFunctor.FreeM
