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
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Defs
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
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Functor
public import Mathlib.Data.Vector.Basic
public import Mathlib.Data.Vector.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Util.Notation3
public import Std.Internal.ForIn
public import dep.PolyFun.Control.Monad.Hom
public import dep.PolyFun.Control.Monad.Support
public import dep.PolyFun.Control.Monad.Support.Instances
public import dep.PolyFun.PFunctor.Basic
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
public import dep.ToMathlib.Control.OptionT
public import dep.ToMathlib.Data.Vector.Induction
public import dep.VCVio.EvalDist.Defs.Support
public import dep.VCVio.OracleComp.Coercions.Add.Basic
public import dep.VCVio.OracleComp.Coercions.SubSpec.Basic
public import dep.VCVio.OracleComp.HasQuery.Basic
public import dep.VCVio.OracleComp.OracleComp
public import dep.VCVio.OracleComp.OracleQuery
public import dep.VCVio.OracleComp.OracleSpec
public import dep.VCVio.OracleComp.ProbComp.Basic
public import dep.VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import dep.VCVio.OracleComp.SimSemantics.QueryImpl.Constructions.Core
public import dep.VCVio.OracleComp.SimSemantics.SimulateQ
public import dep.VCVio.OracleComp.Support
public import dep.dep.CslibCompat.Basic
public import dep.dep.CslibCompat.Free

public section

universe u v w

namespace QueryImpl

variable {ι₁ ι₂} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {m n r : Type u → Type*}

/-- Simplest version of adding queries when all implementations are in the same monad.
The actual add notation for `QueryImpl` uses `QueryImpl.addLift` which adds monad lifting
to this definition for greater flexibility. -/
@[expose] protected def add (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ m) :
    QueryImpl (spec₁ + spec₂) m | .inl t => impl₁ t | .inr t => impl₂ t

/-- Add two `QueryImpl` to get an implementation on the sum of the two `OracleSpec`. -/
instance : HAdd (QueryImpl spec₁ m) (QueryImpl spec₂ m) (QueryImpl (spec₁ + spec₂) m) where
  hAdd := QueryImpl.add

/-- Version of `QueryImpl.add` that also lifts the two implementations to a shared lift monad. -/
@[expose] def addLift {ι₁ ι₂} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {m n r : Type u → Type*} [MonadLiftT m r] [MonadLiftT n r]
    (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ n) : QueryImpl (spec₁ + spec₂) r :=
  (impl₁.liftTarget r) + (impl₂.liftTarget r)

/-- The handler that answers each query in `spec` by making the same query to the ambient
oracles, written `spec.passthrough`. It carries no data: in `spec.passthrough + impl` the target
monad is read off `impl`, and on its own it coerces to `(QueryImpl.id' spec).liftTarget m` for
whichever `m` the context expects. -/
structure Passthrough {ι : Type*} (spec : OracleSpec.{_, u} ι) : Type where
  mk ::

/-- Extend `impl` to `spec₁ + spec₂` by passing the `spec₁` queries through unchanged. The
target monad comes from `impl`, so it never has to be written out. -/
instance {ι₁ ι₂ : Type*} {spec₁ : OracleSpec.{_, u} ι₁} {spec₂ : OracleSpec.{_, u} ι₂}
    {m : Type u → Type v} [MonadLiftT (OracleComp spec₁) m] :
    HAdd (Passthrough spec₁) (QueryImpl spec₂ m) (QueryImpl (spec₁ + spec₂) m) where
  hAdd _ impl := (QueryImpl.id' spec₁).liftTarget m + impl

instance {ι : Type*} {spec : OracleSpec.{_, u} ι} {m : Type u → Type v}
    [MonadLiftT (OracleComp spec) m] : CoeTail (Passthrough spec) (QueryImpl spec m) where
  coe _ := (QueryImpl.id' spec).liftTarget m

section simulateQ_add_liftComp

variable {ι₁' ι₂'}
  {spec₁' : OracleSpec ι₁'} {spec₂' : OracleSpec ι₂'}
  {α : Type u} {m' : Type u → Type v} [Monad m'] [LawfulMonad m']
  (impl₁' : QueryImpl spec₁' m') (impl₂' : QueryImpl spec₂' m')

end simulateQ_add_liftComp

section simulateQ_liftM

variable {ι₁' ι₂'}
  {spec₁' : OracleSpec ι₁'} {spec₂' : OracleSpec ι₂'}
  {α : Type u} {m' : Type u → Type v} [Monad m'] [LawfulMonad m']
  [MonadLiftT (OracleComp spec₁') (OracleComp spec₂')]
  [LawfulMonadLiftT (OracleComp spec₁') (OracleComp spec₂')]

end simulateQ_liftM

section simulateQ_add_add_liftM

variable {ι' ι₁' ι₂'} {spec : OracleSpec ι'} {spec₁ : OracleSpec ι₁'}
  {spec₂ : OracleSpec ι₂'} {m' : Type u → Type v} [Monad m'] [LawfulMonad m']
  (implA : QueryImpl spec m') (implB : QueryImpl (spec₁ + spec₂) m')

end simulateQ_add_add_liftM

section simulateQ_liftM_query_tests

variable {ι} {spec : OracleSpec ι} [Monad m] [LawfulMonad m]

end simulateQ_liftM_query_tests

section simulateQ_addLift_liftM

variable {target : Type u → Type*} [Monad target] [LawfulMonad target]
  {source₁ source₂ : Type u → Type*}

end simulateQ_addLift_liftM

section simulateQ_addLift_add_liftM

open OracleSpec

variable {ι} {spec : OracleSpec ι}
  {target : Type u → Type*} [Monad target] [LawfulMonad target]
  {source₀ : Type u → Type*} [MonadLiftT source₀ target]
  {source : Type u → Type*} [Monad source] [LawfulMonad source]
  [MonadLiftT source target] [LawfulMonadLiftT source target]

end simulateQ_addLift_add_liftM

section simulateQ_optionT_liftM_run

open OracleSpec

end simulateQ_optionT_liftM_run

end QueryImpl

namespace OracleSpec

end OracleSpec
