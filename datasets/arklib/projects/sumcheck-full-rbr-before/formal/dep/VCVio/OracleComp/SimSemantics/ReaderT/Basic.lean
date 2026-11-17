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
public import dep.VCVio.OracleComp.HasQuery.Basic
public import dep.VCVio.OracleComp.OracleComp
public import dep.VCVio.OracleComp.OracleQuery
public import dep.VCVio.OracleComp.OracleSpec
public import dep.VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import dep.dep.CslibCompat.Basic
public import dep.dep.CslibCompat.Free

@[expose] public section

universe u v w x

open OracleSpec

namespace QueryImpl

/-- Given implementations for oracles in `spec₁` and `spec₂` in terms of reader monads for
two different contexts `ρ₁` and `ρ₂`, implement the combined set `spec₁ + spec₂` in terms
of a combined `ρ₁ × ρ₂` state. The binary analogue of `QueryImpl.sigmaReaderT`. -/
def addReaderT {ι₁ : Type u} {ι₂ : Type v}
    {spec₁ : OracleSpec.{u, w} ι₁} {spec₂ : OracleSpec.{v, w} ι₂}
    {m : Type w → Type x} {ρ₁ ρ₂ : Type w}
    (impl₁ : QueryImpl spec₁ (ReaderT ρ₁ m))
    (impl₂ : QueryImpl spec₂ (ReaderT ρ₂ m)) :
    QueryImpl (spec₁ + spec₂) (ReaderT (ρ₁ × ρ₂) m)
  | .inl t => ReaderT.mk fun s => (impl₁ t).run s.1
  | .inr t => ReaderT.mk fun s => (impl₂ t).run s.2

end QueryImpl
