module

public import Batteries.Tactic.Lint
public import Cslib.Foundations.Data.PFunctor.Free
public import Cslib.Init
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Control.Monad.Basic
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Util.Notation3
public import dep.PolyFun.Control.Monad.Hom
public import dep.PolyFun.Control.Trace
public import dep.PolyFun.PFunctor.Basic
public import dep.PolyFun.PFunctor.Chart.Basic
public import dep.PolyFun.PFunctor.Equiv.Basic
public import dep.PolyFun.PFunctor.Free.Displayed
public import dep.PolyFun.PFunctor.Free.Path
public import dep.PolyFun.PFunctor.Lens.Basic
public import dep.PolyFun.PFunctor.Obj
public import dep.PolyFun.PFunctor.Trace
public import dep.dep.CslibCompat.Basic
public import dep.dep.CslibCompat.Free

@[expose] public section

universe uA uB v w

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {α : Type v}

namespace Path

/-- Erase a typed path to the universal list of polynomial events. -/
def trace : (program : FreeM P α) → Path program → PFunctor.TraceList P
  | .pure _, _ => []
  | .liftBind a next, ⟨answer, tail⟩ =>
      ⟨a, answer⟩ :: trace (next answer) tail

/-- Number of operation-answer steps in a completed typed path. -/
def length : (program : FreeM P α) → Path program → Nat
  | .pure _, _ => 0
  | .liftBind _ next, ⟨answer, tail⟩ => length (next answer) tail + 1

/-- The typed path length agrees with the length of its erased event trace. -/
theorem length_eq_length_trace (program : FreeM P α) (path : Path program) :
    length program path = (trace program path).length := sorry

@[deprecated (since := "2026-10-19")] alias length_eq_trace_length := length_eq_length_trace

end Path

end PFunctor.FreeM
