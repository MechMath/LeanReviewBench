module

public import Cslib.Init
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Util.Notation3
public import dep.PolyFun.PFunctor.Basic
public import dep.PolyFun.PFunctor.Obj
public import dep.dep.CslibCompat.Basic

@[expose] public section

universe u v w uA uI

namespace PFunctor

/-- A **handler** for the interface `q`: a monadic choice of direction at each
position (a Kleisli section of `q`). With `m := Id` this is an ordinary
dependent choice of one direction at every position, while a probabilistic
monad gives a randomized choice. -/
abbrev Handler (m : Type u → Type v) (q : PFunctor.{uA, u}) :=
  (a : q.A) → m (q.B a)

namespace Handler

/-- Postcompose every answer computation of a handler by a polymorphic map
between target type constructors. No monad laws are needed for this basic
change-of-target operation. -/
def mapTarget {m : Type u → Type v} {n : Type u → Type w}
    {q : PFunctor.{uA, u}} (transform : ∀ {α : Type u}, m α → n α)
    (handler : PFunctor.Handler m q) : PFunctor.Handler n q :=
  fun position => transform (handler position)

theorem mapTarget_mapTarget {m : Type u → Type v} {n : Type u → Type w}
    {o : Type u → Type uI} {q : PFunctor.{uA, u}}
    (second : ∀ {α : Type u}, n α → o α)
    (first : ∀ {α : Type u}, m α → n α)
    (handler : PFunctor.Handler m q) :
    mapTarget second (mapTarget first handler) =
      mapTarget (fun computation => second (first computation)) handler := sorry

@[deprecated (since := "2026-10-19")] alias mapTarget_comp := mapTarget_mapTarget

end Handler

end PFunctor
