module

public import Cslib.Init
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Util.Notation3
public import dep.PolyFun.PFunctor.Basic
public import dep.PolyFun.PFunctor.Obj
public import dep.VCVio.OracleComp.OracleSpec
public import dep.dep.CslibCompat.Basic

@[expose] public section

universe u v w z

open OracleSpec

/-- Functor to represent queries to oracles specified by an `OracleSpec ι`,
defined to be the object type of the corresponding `PFunctor`.
In particular an element of `OracleQuery spec α` consists of an input value `t : spec.Domain`,
and a continuation `f : spec.Range t → α` specifying what to do with the result.
See `OracleSpec.query` for the case when the continuation `f` just returns the query result. -/
@[reducible]
def OracleQuery {ι : Type u} (spec : OracleSpec.{u, v} ι) :
    Type w → Type (max u v w) :=
  PFunctor.Obj spec.toPFunctor

@[reducible, match_pattern] protected def OracleQuery.mk {ι α} {spec : OracleSpec ι}
    (t : spec.Domain) (f : spec.Range t → α) : OracleQuery spec α := PFunctor.Obj.mk t f

namespace OracleSpec

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}

/-- Query an oracle on in input `t` to get a result in the corresponding `range t`.

Marked `protected`: the bare identifier `query` resolves to `HasQuery.query`
(exported in `VCVio.OracleComp.HasQuery.Basic`), which yields a value in the
ambient monad and lets Lean recover `spec` from the expected type without an
ascription. Use `spec.query t` or `OracleSpec.query t` when you specifically
want the primitive single-query syntax `OracleQuery spec (spec.Range t)`. -/
protected def query (t : spec.Domain) : OracleQuery spec (spec.Range t) :=
  OracleQuery.mk t id

end OracleSpec

namespace OracleSpec.PrimitiveQuery

/-- Inside `open scoped OracleSpec.PrimitiveQuery`, the bare identifier
`query` aliases the primitive single-query syntax `OracleSpec.query`. -/
scoped notation "query" => OracleSpec.query

end OracleSpec.PrimitiveQuery

namespace OracleQuery

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}

/-- The oracle input used in an oracle query. -/
@[inline, reducible]
def input {α} (q : OracleQuery spec α) : spec.Domain := PFunctor.Obj.fst q

/-- The continuation used for the result of an oracle query. -/
@[inline, reducible]
def cont {α} (q : OracleQuery spec α) : spec.Range q.input → α := PFunctor.Obj.snd q

/-- Two oracles queries are equal if they query for the same input and run
extensionally equal continuation on the results of the query. -/
@[ext] lemma ext {α} {q q' : OracleQuery spec α}
    (h : q.input = q'.input) (h' : q.cont ≍ q'.cont) : q = q' := sorry

/-- If an oracle exists and the output type is non-empty then the type of queries is non-empty. -/
instance {α} [Inhabited ι] [Inhabited α] : Inhabited (OracleQuery spec α) :=
  ⟨OracleQuery.mk default (fun _ ↦ default)⟩

/-- If there are no oracles available then the type of queries is empty. -/
instance {α} [h : IsEmpty ι] : IsEmpty (OracleQuery spec α) := sorry

/-- If there is at most one oracle and output, then there is at most one query. -/
instance {α} [h : Subsingleton ι] [h' : Subsingleton α] : Subsingleton (OracleQuery spec α) := sorry

end OracleQuery
