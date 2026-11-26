module

public import Cslib.Init
public import Mathlib.Control.Monad.Writer
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Util.Notation3
public import dep.PolyFun.PFunctor.Basic
public import dep.PolyFun.PFunctor.Handler
public import dep.PolyFun.PFunctor.Obj
public import dep.dep.CslibCompat.Basic

public section

universe u v w uA

namespace PFunctor

namespace Handler

variable {P : PFunctor.{uA, u}}

variable {m : Type u → Type v} {n : Type u → Type w}

/-- Lift every operation of a handler into a new target monad. -/
-- Keep this structural adapter transparent: dependent handler result types
-- frequently need its pointwise reduction during elaboration.
@[expose] def liftTarget (n : Type u → Type w) [MonadLiftT m n]
    (handler : Handler m P) : Handler n P :=
  fun operation => liftM (handler operation)

variable [Monad m]

end Handler

end PFunctor
