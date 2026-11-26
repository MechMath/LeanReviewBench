module

public import Batteries.Tactic.Lint
public import Cslib.Foundations.Data.PFunctor.Free
public import Cslib.Init
public import Mathlib.Control.Monad.Basic
public import Mathlib.Control.Monad.Writer
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Functor
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Util.Notation3
public import dep.PolyFun.Control.Monad.Hom
public import dep.PolyFun.Control.Monad.Support
public import dep.PolyFun.Control.Monad.Support.Instances
public import dep.PolyFun.PFunctor.Basic
public import dep.PolyFun.PFunctor.Equiv.Basic
public import dep.PolyFun.PFunctor.Free.Displayed
public import dep.PolyFun.PFunctor.Free.Path
public import dep.PolyFun.PFunctor.Free.Support
public import dep.PolyFun.PFunctor.Handler
public import dep.PolyFun.PFunctor.Lens.Basic
public import dep.PolyFun.PFunctor.Obj
public import dep.ToCslib.Data.PFunctor.Free.Basic
public import dep.dep.CslibCompat.Basic
public import dep.dep.CslibCompat.Free

@[expose] public section

universe uA uB uA₂ uB₂ uX uY v w

namespace PFunctor

/-- A per-operation predicate-transformer specification for the interface `P` over
an ordered carrier `l`: at each position `a`, transform a postcondition on the
directions of `a` into a precondition. -/
def OpSpec (P : PFunctor.{uA, uB}) (l : Type w) : Type max uA uB w :=
  (a : P.A) → (P.B a → l) → l

namespace OpSpec

variable {P : PFunctor.{uA, uB}} {l : Type w}

/-- Monotonicity of a per-operation spec in its continuation: at every position `a`, `Φ a` is
`Monotone` for the pointwise order on continuations. -/
protected def Monotone [Preorder l] (Φ : OpSpec P l) : Prop :=
  ∀ (a : P.A) ⦃k k' : P.B a → l⦄, (∀ b, k b ≤ k' b) → Φ a k ≤ Φ a k'

@[deprecated (since := "2026-10-19")] alias Mono := OpSpec.Monotone

end OpSpec

namespace FreeM

variable {P : PFunctor.{uA, uB}} {l : Type w} {α β : Type v}

section FreeHandler

variable {Q : PFunctor.{uA₂, uB₂}} {α : Type uB}

end FreeHandler

section Support

open MonadAttach

variable {α : Type v}

end Support

end FreeM

end PFunctor
