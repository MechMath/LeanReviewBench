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
public import Mathlib.Order.CompleteLattice.Basic
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
public import dep.ToMathlib.Control.OptionT
public import dep.ToMathlib.Control.WriterT
public import dep.ToMathlib.Data.Vector.Induction
public import dep.VCVio.EvalDist.Defs.Support
public import dep.VCVio.OracleComp.Coercions.Add.Basic
public import dep.VCVio.OracleComp.Coercions.SubSpec.Basic
public import dep.VCVio.OracleComp.HasQuery.Basic
public import dep.VCVio.OracleComp.OracleComp
public import dep.VCVio.OracleComp.OracleQuery
public import dep.VCVio.OracleComp.OracleSpec
public import dep.VCVio.OracleComp.ProbComp.Basic
public import dep.VCVio.OracleComp.QueryTracking.Structures
public import dep.VCVio.OracleComp.QueryTracking.Tracing.Core
public import dep.VCVio.OracleComp.SimSemantics.Append.Core
public import dep.VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import dep.VCVio.OracleComp.SimSemantics.QueryImpl.Constructions.Core
public import dep.VCVio.OracleComp.SimSemantics.SimulateQ
public import dep.VCVio.OracleComp.Support
public import dep.dep.CslibCompat.Basic
public import dep.dep.CslibCompat.Free

public section

open OracleSpec

universe u

open scoped OracleSpec.PrimitiveQuery

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α β : Type u}

section IsQueryBound

variable {B : Type*}

/-- Generalized query bound parameterized by a budget type, a validity check, and a cost
function. `pure` satisfies any bound; `query t >>= mx` satisfies the bound when
`canQuery t b` and every continuation satisfies the bound at `cost t b`.

This is the specialization of `PFunctor.FreeM.IsRollBound` to
`OracleComp spec α = FreeM spec.toPFunctor α`: an oracle index `t : ι` plays
the role of a polynomial-functor position, and a query continuation
`spec t → OracleComp spec α` is the FreeM `roll` continuation. Most
structural lemmas defer to their FreeM analogues. -/
@[expose]
def IsQueryBound (oa : OracleComp spec α) (budget : B)
    (canQuery : ι → B → Prop) (cost : ι → B → B) : Prop :=
  PFunctor.FreeM.IsRollBound (P := spec.toPFunctor) oa budget canQuery cost

/-- Project an `IsQueryBound` along a budget projection `proj : B → B'`.

If the source bound at budget `b` validates queries at every step, the projected
bound at `proj b` is also validated, provided:
* `h_can`  — whenever a step is allowed in the source (`canQuery t b'`), it is
  allowed in the projection (`canQuery' t (proj b')`);
* `h_cost` — the projection commutes with the cost step on the allowed branch
  (`proj (cost t b') = cost' t (proj b')`).

Typical use: extract a single-coordinate query bound (e.g. `qS`-only) from a
multi-coordinate bound (e.g. `(qS, qH)` from `signHashQueryBound`) by setting
`proj := Prod.fst`. -/
lemma IsQueryBound.proj
    {B' : Type*} (proj : B → B')
    {oa : OracleComp spec α} {b : B}
    {canQuery : ι → B → Prop} {cost : ι → B → B}
    {canQuery' : ι → B' → Prop} {cost' : ι → B' → B'}
    (h_can : ∀ (t : ι) (b' : B), canQuery t b' → canQuery' t (proj b'))
    (h_cost : ∀ (t : ι) (b' : B), canQuery t b' → proj (cost t b') = cost' t (proj b'))
    (h : IsQueryBound oa b canQuery cost) :
    IsQueryBound oa (proj b) canQuery' cost' := sorry

end IsQueryBound

section IsQueryBoundP

/-- Predicate-targeted query bound: a middle ground between `IsQueryBound` and
`IsPerIndexQueryBound` / `IsTotalQueryBound`. `IsQueryBoundP oa p n` says that `oa` makes at most
`n` queries to oracle indices satisfying `p`, with no constraint on the number of queries to
indices where `p` fails.

This is built on the generic `IsQueryBound` with the validity check `¬ p t ∨ 0 < qb` and the cost
function that decrements the budget only on `p`-indices. At `n = 0` it forbids all `p`-queries;
`isQueryBoundP_zero_iff` identifies this with `AllQueriesSatisfy` on the complementary predicate. -/
@[expose]
def IsQueryBoundP (oa : OracleComp spec α) (p : ι → Prop) [DecidablePred p] (n : ℕ) : Prop :=
  IsQueryBound oa n (fun t qb => ¬ p t ∨ 0 < qb)
    (fun t qb => if p t then qb - 1 else qb)

variable (p : ι → Prop) [DecidablePred p]

variable {p}

/-- Projection variant of `IsQueryBound.proj` that lands directly in
`IsQueryBoundP`. Given a vector-budget bound on `oa`, project to a scalar
budget along `proj : B → ℕ` and conclude an `IsQueryBoundP` bound at the
projected coordinate. The two side conditions only have to address `p`-queries:
allowed source steps must keep the projected budget positive when `p` fires
(`h_can`), and the projection must commute with the cost step in the shape
that `IsQueryBoundP` decrements on (`h_cost`).

Typical use: extract a per-predicate scalar bound (e.g. signing-only `qS`
from a `(qS, qH)` pair) without spelling out the `if … then 0 < b else True`
boilerplate at the call site. -/
lemma IsQueryBoundP.proj
    {B : Type*} {oa : OracleComp spec α} {b : B}
    {canQuery : ι → B → Prop} {cost : ι → B → B}
    (proj : B → ℕ)
    (h_can : ∀ (t : ι) (b' : B), canQuery t b' → p t → 0 < proj b')
    (h_cost : ∀ (t : ι) (b' : B), canQuery t b' →
      proj (cost t b') = if p t then proj b' - 1 else proj b')
    (h : IsQueryBound oa b canQuery cost) :
    IsQueryBoundP oa p (proj b) := sorry

end IsQueryBoundP

section AllQueriesSatisfy

/-- Predicate-only query bound: every query `oa` can make, on every response path, is to an
oracle index satisfying `P`.

This is `IsQueryBound` with the unit budget `()`, the validity check `fun t _ => P t`, and the
trivial cost, so nothing is counted and only the reachable oracle indices are constrained.  It
is the `DecidablePred`-free presentation of `IsQueryBoundP oa (fun t => ¬ P t) 0`
(`isQueryBoundP_zero_iff`), through which `IsQueryBoundP.mono`, `IsQueryBoundP.of_imp`,
`isQueryBoundP_bind`, and the predicate-targeted simulation transfers apply to it. -/
def AllQueriesSatisfy (oa : OracleComp spec α) (P : ι → Prop) : Prop :=
  IsQueryBound oa () (fun t _ => P t) (fun _ _ => ())

end AllQueriesSatisfy

section IsPerIndexQueryBound

variable [DecidableEq ι]

/-- Per-index query bound: `qb t` gives the maximum number of queries to oracle `t`.
Each query to `t` decrements `qb t` by one. Recovers the classical notion. -/
abbrev IsPerIndexQueryBound (oa : OracleComp spec α) (qb : ι → ℕ) : Prop :=
  IsQueryBound oa qb (fun t qb => 0 < qb t) (fun t qb => Function.update qb t (qb t - 1))

end IsPerIndexQueryBound

end OracleComp
