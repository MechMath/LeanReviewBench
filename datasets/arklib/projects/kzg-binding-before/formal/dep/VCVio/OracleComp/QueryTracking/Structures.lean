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
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Control.Basic
public import Mathlib.Control.Monad.Basic
public import Mathlib.Control.Monad.Writer
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.FinEnum
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Vector.Basic
public import Mathlib.Data.Vector.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Util.Notation3
public import Std.Internal.ForIn
public import dep.PolyFun.Control.Monad.Hom
public import dep.PolyFun.Control.Trace
public import dep.PolyFun.PFunctor.Basic
public import dep.PolyFun.PFunctor.Chart.Basic
public import dep.PolyFun.PFunctor.Equiv.Basic
public import dep.PolyFun.PFunctor.Handler
public import dep.PolyFun.PFunctor.Handler.Instrumentation
public import dep.PolyFun.PFunctor.Lens.Basic
public import dep.PolyFun.PFunctor.Obj
public import dep.PolyFun.PFunctor.Trace
public import dep.ToCslib.Data.PFunctor.Free.Basic
public import dep.ToMathlib.Control.OptionT
public import dep.ToMathlib.Data.Vector.Induction
public import dep.VCVio.OracleComp.HasQuery.Basic
public import dep.VCVio.OracleComp.OracleComp
public import dep.VCVio.OracleComp.OracleQuery
public import dep.VCVio.OracleComp.OracleSpec
public import dep.VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import dep.VCVio.OracleComp.SimSemantics.SimulateQ
public import dep.dep.CslibCompat.Basic
public import dep.dep.CslibCompat.Free

@[expose] public section

open ENNReal OracleSpec OracleComp

attribute [local implicit_reducible] PFunctor.Idx FreeMonoid

universe u v w

namespace OracleSpec

variable {ι : Type u} {spec : OracleSpec ι}

/-- A partial dependent answer table, ordered by extension of cached responses. -/
structure QueryCache (spec : OracleSpec.{u, v} ι) : Type (max u v) where
  /-- Look up the response stored at an oracle index. -/
  toFn : (t : spec.Domain) → Option (spec.Range t)

namespace QueryCache

instance : CoeFun (QueryCache spec) (fun _ => (t : spec.Domain) → Option (spec.Range t)) :=
  ⟨QueryCache.toFn⟩

/-- Package a partial dependent answer function as a cache. -/
def ofFn (f : (t : spec.Domain) → Option (spec.Range t)) : QueryCache spec := ⟨f⟩

@[simp]
lemma toFn_ofFn (f : (t : spec.Domain) → Option (spec.Range t)) : (ofFn f).toFn = f := sorry

@[simp]
lemma ofFn_toFn (cache : QueryCache spec) : ofFn cache.toFn = cache := sorry

instance : EmptyCollection (QueryCache spec) := ⟨ofFn (fun _ => none)⟩

@[ext]
protected lemma ext {c₁ c₂ : QueryCache spec} (h : ∀ t, c₁ t = c₂ t) : c₁ = c₂ := sorry

/-- Cache lookup is injective. -/
theorem toFn_injective : Function.Injective (@toFn ι spec) := sorry

/-- A cache and its dependent optional lookup table contain the same data. -/
def equivFn : QueryCache spec ≃ ((t : spec.Domain) → Option (spec.Range t)) where
  toFun := toFn
  invFun := ofFn
  left_inv := ofFn_toFn
  right_inv := toFn_ofFn

instance : Inhabited (QueryCache spec) := ⟨∅⟩

instance [DecidableEq ((t : spec.Domain) → Option (spec.Range t))] :
    DecidableEq (QueryCache spec) := fun c₁ c₂ =>
  decidable_of_iff (c₁.toFn = c₂.toFn) toFn_injective.eq_iff

instance [Countable ((t : spec.Domain) → Option (spec.Range t))] :
    Countable (QueryCache spec) := sorry

instance [Finite ((t : spec.Domain) → Option (spec.Range t))] :
    Finite (QueryCache spec) := sorry

instance [Fintype ((t : spec.Domain) → Option (spec.Range t))] :
    Fintype (QueryCache spec) := Fintype.ofEquiv _ equivFn.symm

instance : PartialOrder (QueryCache spec) where
  le c₁ c₂ := ∀ ⦃t⦄ ⦃u : spec.Range t⦄, c₁ t = some u → c₂ t = some u
  le_refl _ _ _ h := h
  le_trans _ _ _ h₁₂ h₂₃ _ _ h := h₂₃ (h₁₂ h)
  le_antisymm a b hab hba := sorry

instance : OrderBot (QueryCache spec) where
  bot := ∅
  bot_le _ := sorry

variable [DecidableEq ι] (cache : QueryCache spec)

/-- Add an index + input pair to the cache by updating the function
(wrapper around `Function.update`). -/
def cacheQuery (t : spec.Domain) (u : spec.Range t) : QueryCache spec :=
  ofFn (Function.update cache t (some u))

section sum

variable {ι₁ ι₂ : Type*} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}

/-- Project a cache for `spec₁ + spec₂` onto `spec₁`. -/
protected def fst (cache : QueryCache (spec₁ + spec₂)) : QueryCache spec₁ :=
  ofFn (fun t => cache (.inl t))

/-- Project a cache for `spec₁ + spec₂` onto `spec₂`. -/
protected def snd (cache : QueryCache (spec₁ + spec₂)) : QueryCache spec₂ :=
  ofFn (fun t => cache (.inr t))

/-- Embed a cache for `spec₁` into one for `spec₁ + spec₂`. -/
protected def inl (cache : QueryCache spec₁) : QueryCache (spec₁ + spec₂) :=
  ofFn (Sum.rec cache (fun _ => none))

/-- Embed a cache for `spec₂` into one for `spec₁ + spec₂`. -/
protected def inr (cache : QueryCache spec₂) : QueryCache (spec₁ + spec₂) :=
  ofFn (Sum.rec (fun _ => none) cache)

instance : Coe (QueryCache spec₁) (QueryCache (spec₁ + spec₂)) := ⟨QueryCache.inl⟩

instance : Coe (QueryCache spec₂) (QueryCache (spec₁ + spec₂)) := ⟨QueryCache.inr⟩

end sum

end QueryCache

/-- Per-index natural counts with the ordinary pointwise additive algebra.
Additive writer instrumentation uses `Multiplicative (QueryCount ι)` as its
monoidal payload; query counts themselves retain the standard function instances. -/
@[reducible] def QueryCount (ι : Type*) := ι → ℕ

namespace QueryCount

end QueryCount

/-- Log of queries represented by a list of dependent product's tagging the oracle's index.
`(t : spec.Domain) × (spec.Range t)` is slightly more restricted as it doesn't
keep track of query ordering between different oracles.

A `QueryLog spec` is morally a free monoid on `Idx spec.toPFunctor`, with
identity `[]` and product `(++)`. By Mathlib reducibility this is exactly
`FreeMonoid (Idx spec.toPFunctor) = TraceList spec.toPFunctor`, so a
trace-valued boundary description such as `BoundaryAction.emit` (in
`PolyFun/Interaction/Open/OpenProcess.lean`) and a per-call `QueryLog`-valued
writer share the same underlying free-monoid carrier.

We do *not* declare a global `Monoid (QueryLog spec)` instance: doing so
would conflict with the `[EmptyCollection ω] [Append ω] → Monad (WriterT ω M)`
instance Mathlib already provides for `WriterT (QueryLog spec) M`, which the
`Std.Do` bridge `WriterTBridge` and the append-based reading `WriterT.AppendWP` rely on. The
`QueryImpl.withTrace`/`withLogging` API instead uses the Append-based
`Monad (WriterT _ _)` directly via `QueryImpl.withTraceAppend`. -/
@[reducible] def QueryLog (spec : OracleSpec.{u, v} ι) : Type (max u v) :=
  List ((t : spec.Domain) × spec.Range t)

namespace QueryLog

instance [DecidableEq ι] [∀ t, DecidableEq (spec.Range t)] : DecidableEq (QueryLog spec) :=
  inferInstanceAs (DecidableEq (List _))

section getQ

/-- Get all the queries with inputs satisfying `p` -/
def getQ (log : QueryLog spec) (p : spec.Domain → Prop) [DecidablePred p] :
    List ((t : spec.Domain) × spec.Range t) :=
  List.foldr (fun ⟨t, u⟩ xs => if p t then ⟨t, u⟩ :: xs else xs) [] log

end getQ

section countQ

/-- Count the number of queries with inputs satisfying `p`. -/
def countQ (log : QueryLog spec) (p : spec.Domain → Prop) [DecidablePred p] : ℕ :=
  (log.getQ p).length

end countQ

section prod

variable {ι₁ ι₂} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}

/-- Get only the portion of the log for queries in `spec₁`. -/
protected def fst (log : QueryLog (spec₁ + spec₂)) : QueryLog spec₁ :=
  log.filterMap (fun | ⟨.inl t, u⟩ => some ⟨t, u⟩ | _ => none)

/-- Get only the portion of the log for queries in `spec₂`. -/
protected def snd (log : QueryLog (spec₁ + spec₂)) : QueryLog spec₂ :=
  log.filterMap (fun | ⟨.inr t, u⟩ => some ⟨t, u⟩ | _ => none)

/-- View a log for `spec₁` as one for `spec₁ + spec₂` by inclusion. -/
protected def inl (log : QueryLog spec₁) : QueryLog (spec₁ + spec₂) :=
  log.map fun ⟨t, u⟩ => ⟨.inl t, u⟩

/-- View a log for `spec₂` as one for `spec₁ + spec₂` by inclusion. -/
protected def inr (log : QueryLog spec₂) : QueryLog (spec₁ + spec₂) :=
  log.map fun ⟨t, u⟩ => ⟨.inr t, u⟩

instance : Coe (QueryLog spec₁) (QueryLog (spec₁ + spec₂)) := ⟨QueryLog.inl⟩

instance : Coe (QueryLog spec₂) (QueryLog (spec₁ + spec₂)) := ⟨QueryLog.inr⟩

end prod

end QueryLog

/-- A store of pre-generated seed values for oracle queries, indexed by oracle.
Maps each oracle index `i` to a list of outputs `List (spec.Range i)`. -/
@[reducible] def QuerySeed (spec : OracleSpec.{u, v} ι) : Type (max u v) :=
  (i : ι) → List (spec.Range i)

namespace QuerySeed

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}

instance : EmptyCollection (QuerySeed spec) := ⟨fun _ => []⟩

@[ext]
protected lemma ext {seed₁ seed₂ : QuerySeed spec} (h : ∀ i, seed₁ i = seed₂ i) :
    seed₁ = seed₂ := sorry

variable [DecidableEq ι]

/-- Replace the seed values at index `i`. -/
def update (seed : QuerySeed spec) (i : ι) (xs : List (spec.Range i)) : QuerySeed spec :=
  Function.update seed i xs

/-- Pop one value from index `i`, returning the consumed value and updated seed when nonempty. -/
def pop (seed : QuerySeed spec) (i : ι) : Option (spec.Range i × QuerySeed spec) :=
  match seed i with
  | [] => none
  | u :: us => some (u, seed.update i us)

/-- Construct a query seed from a list at a single index. -/
def ofList {i : ι} (xs : List (spec.Range i)) : QuerySeed spec :=
  fun j => if h : i = j then h ▸ xs else []

end QuerySeed

end OracleSpec
