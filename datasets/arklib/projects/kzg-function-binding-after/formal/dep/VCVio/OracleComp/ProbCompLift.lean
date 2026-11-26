module

public import Batteries.Control.AlternativeMonad
public import Batteries.Control.OptionT
public import Batteries.Tactic.Lint
public import Batteries.Tactic.Lint.Basic
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
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Functor
public import Mathlib.Data.Vector.Basic
public import Mathlib.Data.Vector.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Defs
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.MeasureTheory.Measure.Comap
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Probability.UniformOn
public import Mathlib.Tactic.Attr.Register
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.EMetricSpace.Weak
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Util.Notation3
public import dep.PolyFun.Control.Monad.Hom
public import dep.PolyFun.Control.Monad.Support
public import dep.PolyFun.Control.Monad.Support.Instances
public import dep.PolyFun.PFunctor.Basic
public import dep.PolyFun.PFunctor.Equiv.Basic
public import dep.PolyFun.PFunctor.Free.Displayed
public import dep.PolyFun.PFunctor.Free.Path
public import dep.PolyFun.PFunctor.Free.Support
public import dep.PolyFun.PFunctor.Lens.Basic
public import dep.PolyFun.PFunctor.Obj
public import dep.ToCslib.Data.PFunctor.Free.Basic
public import dep.ToMathlib.Control.OptionT
public import dep.ToMathlib.Data.Vector.Induction
public import dep.ToMathlib.MeasureTheory.MeasurableSpace.Except
public import dep.ToMathlib.MeasureTheory.MeasurableSpace.Option
public import dep.ToMathlib.MeasureTheory.Measure.Option
public import dep.ToMathlib.MeasureTheory.Measure.Subprobability
public import dep.VCVio.EvalDist.Defs.Measure.Core
public import dep.VCVio.EvalDist.Defs.Measure.ExceptT
public import dep.VCVio.EvalDist.Defs.Measure.Failure
public import dep.VCVio.EvalDist.Defs.Measure.OptionT
public import dep.VCVio.EvalDist.Defs.Semantics.Core
public import dep.VCVio.EvalDist.Defs.Support
public import dep.VCVio.EvalDist.PFunctorMeasure.Core
public import dep.VCVio.EvalDist.ProbabilityNotation
public import dep.VCVio.EvalDist.ProbabilityNotation.Attr
public import dep.VCVio.OracleComp.EvalDist.AnswerMeasure
public import dep.VCVio.OracleComp.HasQuery.Basic
public import dep.VCVio.OracleComp.OracleComp
public import dep.VCVio.OracleComp.OracleQuery
public import dep.VCVio.OracleComp.OracleSpec
public import dep.VCVio.OracleComp.ProbComp.Basic
public import dep.VCVio.OracleComp.Support
public import dep.dep.CslibCompat.Basic
public import dep.dep.CslibCompat.Free

@[expose] public section

open MeasureTheory

universe v w

/-- Bundled way to lift plain probabilistic computations into an ambient monad `m`.

Intuitively, this is the capability "sample fresh public randomness inside `m`". We package it as
a monad homomorphism so it composes lawfully with `pure` and `bind`. -/
structure ProbCompLift (m : Type → Type v) [Monad m] where
  /-- Inject a plain `ProbComp` computation into `m`. -/
  liftProbComp : ProbComp →ᵐ m

namespace ProbCompLift

/-- The identity lift on `ProbComp` itself. -/
def id : ProbCompLift ProbComp where
  liftProbComp := MonadHom.id ProbComp

end ProbCompLift

/-- Common runtime bundle for crypto games in an ambient monad `m`.

This packages the two capabilities that security experiments usually need together:

1. `SemanticsVia m` to observe successful experiment outputs.
2. `ProbCompLift m` to sample fresh public randomness inside `m`.

The bundle is kept separate from the core scheme definitions so that executable scheme data does
not become noncomputable merely by carrying denotational semantics. -/
structure ProbCompRuntime (m : Type → Type v) [Monad m] where
  /-- Bundled successful-output measure semantics for the ambient monad. -/
  toSemanticsVia : SemanticsVia.{0, v, w} m
  /-- Bundled injection of plain probabilistic sampling into the ambient monad. -/
  toProbCompLift : ProbCompLift m
  /-- Observing a measurable map agrees with pushing the output measure forward. -/
  evalDist_map_eq : ∀ {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β), Measurable f → ∀ mx : m α,
      toSemanticsVia.evalDist (f <$> mx) =
        (toSemanticsVia.evalDist mx).map f

namespace ProbCompRuntime

variable {m : Type → Type v} [Monad m] {α : Type}

/-- Observe an ambient computation by its successful-output measure. -/
noncomputable def evalDist (runtime : ProbCompRuntime m) [MeasurableSpace α]
    (mx : m α) : Measure α :=
  runtime.toSemanticsVia.evalDist mx

/-- Every runtime observation is a subprobability measure. Registering the bundled mass bound as
an instance lets the ordinary measure API discharge finite-mass and `≤ 1` side conditions. -/
instance (runtime : ProbCompRuntime m) [MeasurableSpace α] (mx : m α) :
    IsSubprobabilityMeasure (runtime.evalDist mx) := sorry

/-- Runtime observation commutes with measurable maps. -/
@[simp]
lemma evalDist_map (runtime : ProbCompRuntime m) {β : Type}
    [MeasurableSpace α] [MeasurableSpace β] (f : α → β) (hf : Measurable f) (mx : m α) :
    runtime.evalDist (f <$> mx) = (runtime.evalDist mx).map f := sorry

/-- Lift a plain `ProbComp` computation into the ambient monad using the runtime's public
randomness capability. -/
def liftProbComp (runtime : ProbCompRuntime m) : ProbComp →ᵐ m :=
  runtime.toProbCompLift.liftProbComp

/-- Canonical runtime for `ProbComp` itself. -/
noncomputable def probComp : ProbCompRuntime ProbComp where
  toSemanticsVia := SemanticsVia.ofEvalDistSemantics ProbComp
  toProbCompLift := ProbCompLift.id
  evalDist_map_eq _f hf mx := _root_.evalDist_map mx hf

/-- The canonical `ProbComp` runtime assigns every computation a probability measure. -/
instance [MeasurableSpace α] (mx : ProbComp α) :
    MeasureTheory.IsProbabilityMeasure (probComp.evalDist mx) := sorry

end ProbCompRuntime
