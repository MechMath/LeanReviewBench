module

public import Batteries.Control.AlternativeMonad
public import Batteries.Control.OptionT
public import Mathlib.Control.Basic
public import Mathlib.Control.Monad.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.EquivFin
public import dep.PolyFun.Control.Monad.Hom

@[expose] public section

universe u v w

namespace OptionT

variable {m : Type u → Type v} {n : Type u → Type w}
  (f : {α : Type u} → m α → n α) {α β γ : Type u}

section mapM

/-- Canonical lifting of a map from `m α → n α` to one from `OptionT m α → n α`
given an `Alternative n` instance to handle failure. -/
protected def mapM {m : Type u → Type v} {n : Type u → Type w}
    [AlternativeMonad n] (f : {α : Type u} → m α → n α)
    {α : Type u} (x : OptionT m α) : n α :=
  do (← f x.run).getM

end mapM

end OptionT
