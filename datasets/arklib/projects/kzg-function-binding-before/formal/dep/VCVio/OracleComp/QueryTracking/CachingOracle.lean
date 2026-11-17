module

public import Batteries.Control.AlternativeMonad
public import Batteries.Control.Lemmas
public import Batteries.Control.OptionT
public import Batteries.Tactic.Lint
public import Batteries.Tactic.Lint.Basic
public import Cslib.Foundations.Control.Monad.Free
public import Cslib.Foundations.Control.Monad.IsMonadHom
public import Cslib.Foundations.Control.Monad.IsMonadHom.List
public import Cslib.Foundations.Data.PFunctor.Free
public import Cslib.Init
public import Lean.PrettyPrinter.Delaborator.Basic
public import Lean.PrettyPrinter.Formatter
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
public import Mathlib.Data.FunLike.IsApply
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
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.MeasureTheory.Measure.Comap
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Probability.UniformOn
public import Mathlib.Tactic.Attr.Register
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.EMetricSpace.Weak
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Util.Notation3
public import Std.Internal.ForIn
public import dep.PolyFun.Control.Monad.Hom
public import dep.PolyFun.Control.Monad.Support
public import dep.PolyFun.Control.Monad.Support.Instances
public import dep.PolyFun.Control.Trace
public import dep.PolyFun.PFunctor.Basic
public import dep.PolyFun.PFunctor.Bound
public import dep.PolyFun.PFunctor.Chart.Basic
public import dep.PolyFun.PFunctor.Equiv.Basic
public import dep.PolyFun.PFunctor.Free.Displayed
public import dep.PolyFun.PFunctor.Free.Path
public import dep.PolyFun.PFunctor.Free.Support
public import dep.PolyFun.PFunctor.Free.WP
public import dep.PolyFun.PFunctor.Handler
public import dep.PolyFun.PFunctor.Handler.Instrumentation
public import dep.PolyFun.PFunctor.Lens.Basic
public import dep.PolyFun.PFunctor.Lens.Cartesian
public import dep.PolyFun.PFunctor.Obj
public import dep.PolyFun.PFunctor.Trace
public import dep.ToCslib.Data.PFunctor.Free.Basic
public import dep.ToMathlib.Control.OptionT
public import dep.ToMathlib.Control.WriterT
public import dep.ToMathlib.Data.Vector.Induction
public import dep.ToMathlib.MeasureTheory.MeasurableSpace.Option
public import dep.ToMathlib.MeasureTheory.Measure.Option
public import dep.ToMathlib.MeasureTheory.Measure.Subprobability
public import dep.VCVio.EvalDist.Defs.Measure.Core
public import dep.VCVio.EvalDist.Defs.Measure.Failure
public import dep.VCVio.EvalDist.Defs.Measure.OptionT
public import dep.VCVio.EvalDist.Defs.Support
public import dep.VCVio.EvalDist.EvalDistEq
public import dep.VCVio.EvalDist.PFunctorMeasure.Core
public import dep.VCVio.EvalDist.ProbabilityNotation
public import dep.VCVio.EvalDist.ProbabilityNotation.Attr
public import dep.VCVio.OracleComp.Coercions.Add.Basic
public import dep.VCVio.OracleComp.Coercions.SubSpec.Basic
public import dep.VCVio.OracleComp.EvalDist.AnswerMeasure
public import dep.VCVio.OracleComp.HasQuery.Basic
public import dep.VCVio.OracleComp.OracleComp
public import dep.VCVio.OracleComp.OracleQuery
public import dep.VCVio.OracleComp.OracleSpec
public import dep.VCVio.OracleComp.ProbComp.Basic
public import dep.VCVio.OracleComp.QueryTracking.Structures
public import dep.VCVio.OracleComp.SimSemantics.Append.Core
public import dep.VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import dep.VCVio.OracleComp.SimSemantics.SimulateQ
public import dep.VCVio.OracleComp.SimSemantics.StateT.PreservesInv
public import dep.VCVio.OracleComp.Support
public import dep.dep.CslibCompat.Basic
public import dep.dep.CslibCompat.Free

@[expose] public section

open OracleComp OracleSpec

universe u v w

open scoped OracleSpec.PrimitiveQuery

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι}

namespace QueryImpl

variable {m : Type u → Type v} [Monad m]

/-- Modify a query implementation to cache previous call and return that output in the future. -/
def withCaching (so : QueryImpl spec m) : QueryImpl spec (StateT spec.QueryCache m) :=
  fun t => do match (← get) t with
    | Option.some u => return u
    | Option.none =>
        let u ← so t
        modifyGet fun cache => (u, cache.cacheQuery t u)

section CachingAux

variable {Q : Type w} {m' : Type (max u w) → Type v} [Monad m']

end CachingAux

section CacheAuxProjection

variable {Q : Type u}

variable [LawfulMonad m]

end CacheAuxProjection

section CachingAuxInvariant

variable {Q : Type w} {m' : Type (max u w) → Type v} [Monad m'] [LawfulMonad m']
  [MonadAttach m'] [ExactMonadAttach m']

end CachingAuxInvariant

section CacheMonotonicity

section queryAll

variable {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec.{0, 0} ι₀} {m₀ : Type → Type v}
  [Monad m₀] [LawfulMonad m₀] [MonadAttach m₀] [ExactMonadAttach m₀] (so : QueryImpl spec₀ m₀)

end queryAll

end CacheMonotonicity

section QueryBound

variable {ι' : Type u} {spec' : OracleSpec ι'}

end QueryBound

end QueryImpl

namespace OracleComp

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι}
  {ι' : Type u} {spec' : OracleSpec ι'} {α : Type u}

end OracleComp

/-- Oracle for caching queries to the oracles in `spec`, querying fresh values if needed. -/
@[inline, reducible] def OracleSpec.cachingOracle :
    QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
  (QueryImpl.ofLift spec (OracleComp spec)).withCaching

namespace cachingOracle

end cachingOracle

section withCacheOverlay

/-- Run an `OracleComp` with a `QueryCache` as a priority layer over the real oracle.
Cached entries are returned directly (no oracle query), misses fall through to the real
oracle and get cached for subsequent lookups within the same computation.

This is the fundamental "programmable random oracle" primitive: pre-fill the cache with
programmed entries, then run the computation. Concretely:

  `withCacheOverlay cache oa = StateT.run' (simulateQ cachingOracle oa) cache`

Key properties:
- `withCacheOverlay ∅ oa` deduplicates queries but is otherwise equivalent to `oa`.
- `withCacheOverlay cache (query t)` returns `v` without an external query when
  `cache t = some v`, and queries the real oracle when `cache t = none`.

The cache-parametric runtime built on top of this combinator lives in
`VCVio.CryptoFoundations.FiatShamir.Sigma` as `FiatShamir.runtimeWithCache cache`, with
`FiatShamir.runtime` defined as `runtimeWithCache ∅`. -/
def OracleSpec.withCacheOverlay {α : Type u} (cache : spec.QueryCache) (oa : OracleComp spec α) :
    OracleComp spec α :=
  StateT.run' (simulateQ spec.cachingOracle oa) cache

end withCacheOverlay

namespace OracleComp

end OracleComp
