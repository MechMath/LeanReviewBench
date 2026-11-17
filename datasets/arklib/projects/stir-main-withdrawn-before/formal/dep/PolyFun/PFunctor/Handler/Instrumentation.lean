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

/-- Run an effect before handling each operation.

The inserted effect is sequenced before the underlying handler. Whether its
effects remain observable if that handler subsequently fails depends on the
target monad's transformer order; for example, `WriterT` over `Option` discards
the log together with a failed result. The inserted effect's value is
discarded. -/
def preInsert [Monad n] [MonadLiftT m n] {α : Type u}
    (handler : Handler m P) (before : P.A → n α) : Handler n P :=
  fun operation => before operation *> liftM (handler operation)

/-- Run an effect after handling each operation.

The inserted effect may depend on the response and is skipped if the
underlying handler fails. Its result is discarded. -/
def postInsert [Monad n] [MonadLiftT m n] {α : Type u}
    (handler : Handler m P) (after : (operation : P.A) → P.B operation → n α) :
    Handler n P :=
  fun operation => do
    let response ← liftM (handler operation)
    let _ ← after operation response
    return response

variable [Monad m]

/-- Record a response-independent trace before each handled operation. -/
def withTraceBefore {ω : Type u} [Monoid ω]
    (handler : Handler m P) (trace : P.A → ω) : Handler (WriterT ω m) P :=
  handler.preInsert fun operation => tell (trace operation)

/-- Record a response-dependent trace after each handled operation. -/
def withTrace {ω : Type u} [Monoid ω]
    (handler : Handler m P) (trace : (operation : P.A) → P.B operation → ω) :
    Handler (WriterT ω m) P :=
  handler.postInsert fun operation response => tell (trace operation response)

/-- Append-flavoured response-independent tracing. -/
def withTraceAppendBefore {ω : Type u} [EmptyCollection ω] [Append ω]
    (handler : Handler m P) (trace : P.A → ω) : Handler (WriterT ω m) P :=
  handler.preInsert fun operation => tell (trace operation)

/-- Append-flavoured response-dependent tracing. -/
def withTraceAppend {ω : Type u} [EmptyCollection ω] [Append ω]
    (handler : Handler m P) (trace : (operation : P.A) → P.B operation → ω) :
    Handler (WriterT ω m) P :=
  handler.postInsert fun operation response => tell (trace operation response)

end Handler

end PFunctor
