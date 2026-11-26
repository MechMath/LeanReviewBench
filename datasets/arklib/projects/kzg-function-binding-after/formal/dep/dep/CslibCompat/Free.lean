module

public import Cslib.Foundations.Data.PFunctor.Free

@[expose] public section

namespace PFunctor.FreeM

universe u uB v w z

variable {P : PFunctor.{u, uB}} {α : Type v} {β : Type w} {γ : Type z}

@[simp]
theorem map_pure (f : α → β) (x : α) : map f (pure x : P.FreeM α) = pure (f x) := sorry

@[simp]
theorem map_bind (f : β → γ) (x : P.FreeM α) (cont : α → P.FreeM β) :
    map f (x.bind cont) = x.bind fun a => (cont a).map f := sorry

end PFunctor.FreeM
