module

public import Batteries.Tactic.Lint
public import Cslib.Foundations.Data.PFunctor.Free
public import Cslib.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Control.Monad.Basic
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Util.Notation3
public import dep.PolyFun.Control.Monad.Hom
public import dep.PolyFun.PFunctor.Basic
public import dep.PolyFun.PFunctor.Equiv.Basic
public import dep.PolyFun.PFunctor.Lens.Basic
public import dep.PolyFun.PFunctor.Obj
public import dep.ToCslib.Data.PFunctor.Free.Basic
public import dep.VCVio.OracleComp.HasQuery.Basic
public import dep.VCVio.OracleComp.OracleQuery
public import dep.VCVio.OracleComp.OracleSpec
public import dep.dep.CslibCompat.Basic
public import dep.dep.CslibCompat.Free

@[expose] public section

universe u v w

open OracleSpec

/-- `OracleComp spec α` represents computations with oracle access to oracles in `spec`,
where the final return value has type `α`, represented as a free monad over the `PFunctor`
corresponding to `spec.` -/
@[reducible]
def OracleComp {ι : Type u} (spec : OracleSpec.{u, v} ι) :
    Type w → Type (max u v w) :=
  PFunctor.FreeM spec.toPFunctor

variable {α β γ : Type v} {ι} {spec : OracleSpec.{u, v} ι}

namespace OracleComp

open scoped OracleSpec.PrimitiveQuery

/-- Make one oracle query at input `t`, then continue with `k` on the response.

This is the `PFunctor.FreeM.liftBind` constructor specialized to `OracleComp`;
the `@[match_pattern]` attribute makes it usable both as a term and as a
`match` pattern. -/
@[match_pattern, reducible]
def queryBind {α} (t : spec.Domain) (k : spec.Range t → OracleComp spec α) :
    OracleComp spec α :=
  PFunctor.FreeM.liftBind t k

/-- Manually lift an `OracleQuery` to an `OracleComp`. -/
@[reducible]
protected def lift {ι} {spec : OracleSpec ι} {α} (q : OracleQuery spec α) :
    OracleComp spec α := liftM q

/-- Structural recursion eliminator on `OracleComp` exposing the high-level
`pure` / `queryBind` alternatives, with an induction hypothesis on every
continuation in the `queryBind` case. Registered as the default `induction`
eliminator so that
`induction oa with | pure x => ... | queryBind t k ih => ...`
works transparently on top of the free-monad substrate. -/
@[elab_as_elim, induction_eliminator]
def recOn {α} {motive : OracleComp spec α → Sort*}
    (oa : OracleComp spec α)
    (pure : (x : α) → motive (PFunctor.FreeM.pure x : OracleComp spec α))
    (queryBind : (t : spec.Domain) →
      (k : spec.Range t → OracleComp spec α) →
      ((u : spec.Range t) → motive (k u)) →
      motive (OracleComp.queryBind (spec := spec) t k)) :
    motive oa :=
  match oa with
  | .pure x => pure x
  | .queryBind t k => queryBind t k (fun u => recOn (k u) pure queryBind)

section construct

/-- Version of `construct` with automatic induction on the `query` in when defining the
`query_bind` case. Can be useful with decidable equality or finiteness of the answer types.
`mapM`/`simulateQ` is usually preferable to this if the object being constructed is a monad. -/
@[elab_as_elim]
protected def construct {α}
    {C : OracleComp spec α → Type*}
    (pure : (a : α) → C (pure a))
    (query_bind : (t : spec.Domain) →
      (oa : spec.Range t → OracleComp spec α) →
      ((u : spec.Range t) → C (oa u)) → C (query t >>= oa))
    (oa : OracleComp spec α) : C oa :=
  OracleComp.recOn oa pure query_bind

end construct

section noConfusion

variable (x : α) (y : β) (t : spec.Domain) (u : spec.Range t)
  (oa : β → OracleComp spec α) (ou : spec.Range t → OracleComp spec α)

end noConfusion

section inj

end inj

end OracleComp
