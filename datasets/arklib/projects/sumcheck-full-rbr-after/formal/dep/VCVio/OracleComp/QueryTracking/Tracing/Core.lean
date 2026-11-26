module

public import Batteries.Control.AlternativeMonad
public import Batteries.Control.OptionT
public import Batteries.Tactic.Lint
public import Batteries.Tactic.Lint.Basic
public import Cslib.Foundations.Control.Monad.IsMonadHom
public import Cslib.Foundations.Control.Monad.IsMonadHom.List
public import Cslib.Foundations.Data.PFunctor.Free
public import Cslib.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Control.Basic
public import Mathlib.Control.Monad.Basic
public import Mathlib.Control.Monad.Writer
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.FinEnum
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Functor
public import Mathlib.Data.Vector.Basic
public import Mathlib.Data.Vector.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Util.Notation3
public import Std.Internal.ForIn
public import dep.PolyFun.Control.Monad.Hom
public import dep.PolyFun.Control.Monad.Support
public import dep.PolyFun.Control.Monad.Support.Instances
public import dep.PolyFun.Control.Trace
public import dep.PolyFun.PFunctor.Basic
public import dep.PolyFun.PFunctor.Chart.Basic
public import dep.PolyFun.PFunctor.Equiv.Basic
public import dep.PolyFun.PFunctor.Free.Displayed
public import dep.PolyFun.PFunctor.Free.Path
public import dep.PolyFun.PFunctor.Free.Support
public import dep.PolyFun.PFunctor.Handler
public import dep.PolyFun.PFunctor.Handler.Instrumentation
public import dep.PolyFun.PFunctor.Lens.Basic
public import dep.PolyFun.PFunctor.Obj
public import dep.PolyFun.PFunctor.Trace
public import dep.ToMathlib.Control.OptionT
public import dep.ToMathlib.Control.WriterT
public import dep.ToMathlib.Data.Vector.Induction
public import dep.VCVio.EvalDist.Defs.Support
public import dep.VCVio.OracleComp.HasQuery.Basic
public import dep.VCVio.OracleComp.OracleComp
public import dep.VCVio.OracleComp.OracleQuery
public import dep.VCVio.OracleComp.OracleSpec
public import dep.VCVio.OracleComp.QueryTracking.Structures
public import dep.VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import dep.VCVio.OracleComp.SimSemantics.QueryImpl.Constructions.Core
public import dep.VCVio.OracleComp.SimSemantics.SimulateQ
public import dep.VCVio.OracleComp.Support
public import dep.dep.CslibCompat.Basic
public import dep.dep.CslibCompat.Free

public section

open OracleSpec OracleComp

universe u v w

variable {ι : Type u} {spec : OracleSpec ι} {α β γ : Type u}

namespace QueryImpl

variable {m : Type u → Type v} [Monad m]

section withTraceBefore

variable {ω : Type u} [Monoid ω]

/-- Wrap an oracle implementation so that each query records `traceFn t` in
the writer `ω` *before* running the handler. The trace value depends only on
the query. Failure in the base monad can discard the entire writer result. -/
abbrev withTraceBefore (so : QueryImpl spec m) (traceFn : spec.Domain → ω) :
    QueryImpl spec (WriterT ω m) :=
  PFunctor.Handler.withTraceBefore (P := spec.toPFunctor) so traceFn

end withTraceBefore

section withTrace

variable {ω : Type u} [Monoid ω]

/-- Wrap an oracle implementation so that each query records
`traceFn t u` in the writer `ω` *after* the handler returns response `u`.
A handler failure skips the trace (the response never materialised). -/
abbrev withTrace (so : QueryImpl spec m)
    (traceFn : (t : spec.Domain) → spec.Range t → ω) :
    QueryImpl spec (WriterT ω m) :=
  PFunctor.Handler.withTrace (P := spec.toPFunctor) so traceFn

end withTrace

section withTraceAppendBefore

variable {ω : Type u} [EmptyCollection ω] [Append ω]

/-- Append-flavoured analogue of `withTraceBefore`: each query records
`traceFn t` in the writer `ω` *before* running the handler, and `WriterT`
uses the `[EmptyCollection ω] [Append ω]` `Monad` instance (`tell` is a single
push, `bind` concatenates with `++`). The trace value depends only on the
query. Failure in the base monad can discard the entire writer result. -/
abbrev withTraceAppendBefore (so : QueryImpl spec m) (traceFn : spec.Domain → ω) :
    QueryImpl spec (WriterT ω m) :=
  PFunctor.Handler.withTraceAppendBefore (P := spec.toPFunctor) so traceFn

end withTraceAppendBefore

section withTraceAppend

variable {ω : Type u} [EmptyCollection ω] [Append ω]

/-- Append-flavoured analogue of `withTrace`: each query records
`traceFn t u` in the writer `ω` *after* the handler returns response `u`,
using the `[EmptyCollection ω] [Append ω]` `Monad (WriterT ω m)` instance.
A handler failure skips the trace (the response never materialised). -/
abbrev withTraceAppend (so : QueryImpl spec m)
    (traceFn : (t : spec.Domain) → spec.Range t → ω) :
    QueryImpl spec (WriterT ω m) :=
  PFunctor.Handler.withTraceAppend (P := spec.toPFunctor) so traceFn

end withTraceAppend

end QueryImpl
