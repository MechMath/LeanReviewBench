module

public import Batteries.Tactic.Lint
public import Cslib.Foundations.Data.PFunctor.Free
public import Cslib.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Control.Monad.Basic
public import Mathlib.Control.Monad.Writer
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Util.Notation3
public import dep.PolyFun.Control.Monad.Hom
public import dep.PolyFun.PFunctor.Basic
public import dep.PolyFun.PFunctor.Equiv.Basic
public import dep.PolyFun.PFunctor.Handler
public import dep.PolyFun.PFunctor.Handler.Instrumentation
public import dep.PolyFun.PFunctor.Lens.Basic
public import dep.PolyFun.PFunctor.Obj
public import dep.ToCslib.Data.PFunctor.Free.Basic
public import dep.VCVio.OracleComp.HasQuery.Basic
public import dep.VCVio.OracleComp.OracleComp
public import dep.VCVio.OracleComp.OracleQuery
public import dep.VCVio.OracleComp.OracleSpec
public import dep.dep.CslibCompat.Basic
public import dep.dep.CslibCompat.Free

@[expose] public section

open OracleSpec OracleComp

universe u v w

open scoped OracleSpec.PrimitiveQuery

/-- A monadic handler for the polynomial interface induced by `spec`.

Concretely, this maps every oracle input `x` to a computation returning an
answer of type `spec.Range x`. It extends first to `OracleQuery spec` by
applying the continuation, then to `OracleComp spec` by preserving `pure` and
`bind`; see `QueryImpl.mapQuery` and `simulateQ`. -/
@[reducible] def QueryImpl {ι} (spec : OracleSpec ι) (m : Type u → Type v) :=
  (x : spec.Domain) → m (spec.Range x)

namespace QueryImpl

variable {ι} {spec : OracleSpec ι} {m : Type u → Type v} {n : Type u → Type w}

instance [∀ t, Inhabited (spec.Range t)] [Pure m] : Inhabited (QueryImpl spec m) where
  default _ := pure default

/-- Two query implementations are the same if they are the same on all query inputs. -/
@[ext] lemma ext {so so' : QueryImpl spec m}
    (h : ∀ x : spec.Domain, so x = so' x) : so = so' := sorry

section liftTarget

/-- Compatibility alias for the generic polynomial-handler target lift. -/
abbrev liftTarget (n : Type u → Type*) [MonadLiftT m n]
    (impl : QueryImpl spec m) : QueryImpl spec n :=
  PFunctor.Handler.liftTarget (P := spec.toPFunctor) n impl

end liftTarget

section id

/-- Identity implementation for queries, sending `q : OracleQuery spec α` to itself. -/
protected def id (spec : OracleSpec ι) :
    QueryImpl spec (OracleQuery spec) := query

end id

section ofLift

/-- Given that queries in `spec` lift to the monad `m` we get an implementation via lifting. -/
def ofLift (spec : OracleSpec ι) (m : Type u → Type v)
    [MonadLiftT (OracleQuery spec) m] : QueryImpl spec m :=
  fun t : spec.Domain => liftM (query t)

end ofLift

section ofFn

/-- View a function from oracle inputs to outputs as an implementation in the `Id` monad.
Can be used to run a computation to get a specific value. -/
def ofFn (f : (t : spec.Domain) → spec.Range t) :
    QueryImpl spec Id := f

end ofFn

section ofFn?

/-- Version of `ofFn` that allows queries to fail to return a value. -/
def ofFn? (f : (t : spec.Domain) → Option (spec.Range t)) :
    QueryImpl spec Option := f

end ofFn?

end QueryImpl

namespace HasQuery

variable {ι} {spec : OracleSpec ι} {m : Type u → Type v}

end HasQuery
