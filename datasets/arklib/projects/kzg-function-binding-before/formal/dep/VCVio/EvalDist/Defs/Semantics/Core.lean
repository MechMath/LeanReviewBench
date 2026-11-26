module

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Control.Basic
public import Mathlib.Control.Monad.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.FinEnum
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.FunLike.IsApply
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Vector.Basic
public import Mathlib.Data.Vector.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Defs
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.MeasureTheory.Measure.Comap
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.EMetricSpace.Weak
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import dep.PolyFun.Control.Monad.Hom
public import dep.ToMathlib.Data.Vector.Induction
public import dep.ToMathlib.MeasureTheory.MeasurableSpace.Except
public import dep.ToMathlib.MeasureTheory.MeasurableSpace.Option
public import dep.ToMathlib.MeasureTheory.Measure.Option
public import dep.ToMathlib.MeasureTheory.Measure.Subprobability
public import dep.VCVio.EvalDist.Defs.Measure.Core
public import dep.VCVio.EvalDist.Defs.Measure.ExceptT
public import dep.VCVio.EvalDist.Defs.Measure.Failure
public import dep.VCVio.EvalDist.Defs.Measure.OptionT

public section

open MeasureTheory

universe u v w

/-- Bundled subprobability semantics factoring a surface monad through an internal monad.

`interpret` is a monad morphism into the internal monad; `observe` need not be one, and takes
the output measurable space explicitly, since observing a `Measure α` requires one. Running the
internal computation may fix hidden state or discard auxiliary structure before the final
denotation is exposed. Failure or nontermination is represented by missing mass. -/
structure SemanticsVia (m : Type u → Type v) [Monad m] where
  /-- Internal semantic monad. -/
  Sem : Type u → Type w
  /-- Monad structure carried by the internal semantics. -/
  [instMonadSem : Monad Sem]
  /-- Interpret a surface computation in the internal semantic monad. -/
  interpret : m →ᵐ Sem
  /-- Observe successful outputs as a Mathlib measure. -/
  observe : {α : Type u} → [MeasurableSpace α] → Sem α → Measure α
  /-- Every observation has total mass at most one. -/
  observe_apply_univ_le_one : ∀ {α : Type u} [MeasurableSpace α] (mx : Sem α),
    observe mx Set.univ ≤ 1

instance {m : Type u → Type v} [Monad m] (sem : SemanticsVia m) : Monad sem.Sem :=
  sem.instMonadSem

namespace SemanticsVia

variable {m : Type u → Type v} [Monad m] {α : Type u}

/-- The visible measure denoted by a computation under a bundled semantics. -/
@[expose]
noncomputable def evalDist (sem : SemanticsVia m) [MeasurableSpace α]
    (mx : m α) : Measure α :=
  sem.observe (sem.interpret mx)

/-- Every bundled observation is a subprobability measure. -/
instance evalDist.instIsSubprobabilityMeasure (sem : SemanticsVia m)
    [MeasurableSpace α] (mx : m α) : IsSubprobabilityMeasure (sem.evalDist mx) := sorry

/-- Package a global `EvalDistSemantics` instance as a local bundled semantics. -/
@[expose]
protected noncomputable def ofEvalDistSemantics (m : Type u → Type v) [Monad m]
    [EvalDistSemantics m] : SemanticsVia m where
  Sem := m
  instMonadSem := inferInstance
  interpret := MonadHom.id m
  observe := fun mx ↦ EvalDistSemantics.denote mx
  observe_apply_univ_le_one := fun mx ↦ EvalDistSemantics.apply_univ_le_one mx

/-- Bundling a lossless denotation preserves its probability-measure certificate. -/
instance ofEvalDistSemantics.instIsProbabilityMeasure [EvalDistSemantics m]
    [MeasurableSpace α] (mx : m α) [IsProbabilityMeasure 𝒟[mx]] :
    IsProbabilityMeasure ((SemanticsVia.ofEvalDistSemantics m).evalDist mx) := sorry

/-- Bundle the successful-output semantics of an optional computation. Its observation
measures present outputs and retains any underlying failure as missing mass. -/
@[expose]
protected noncomputable def optionT (m : Type u → Type v) [Monad m]
    [EvalDistSemantics m] : SemanticsVia (OptionT m) where
  Sem := OptionT m
  instMonadSem := inferInstance
  interpret := MonadHom.id (OptionT m)
  observe := fun mx ↦ (𝒟[mx.run]).comap some
  observe_apply_univ_le_one := fun mx ↦
    sorry

/-- Optional bundling preserves a known successful-output probability certificate. -/
instance optionT.instIsProbabilityMeasure [EvalDistSemantics m]
    [MeasurableSpace α] (mx : OptionT m α) [IsProbabilityMeasure 𝒟[mx]] :
    IsProbabilityMeasure ((SemanticsVia.optionT m).evalDist mx) := sorry

/-- Bundle the successful-output semantics of `ExceptT`. Errors remain observable
in the run measure and are discarded only by the `Except.ok` observation at this boundary. -/
@[expose]
protected noncomputable def exceptT (ε : Type u) [MeasurableSpace ε]
    (m : Type u → Type v) [Monad m] [EvalDistSemantics m] :
    SemanticsVia (ExceptT ε m) where
  Sem := ExceptT ε m
  instMonadSem := inferInstance
  interpret := MonadHom.id (ExceptT ε m)
  observe := fun mx ↦ (𝒟[mx.run]).comap Except.ok
  observe_apply_univ_le_one := fun mx ↦
    sorry

/-- Exceptional bundling preserves a known successful-output probability certificate. -/
instance exceptT.instIsProbabilityMeasure {ε : Type u} [MeasurableSpace ε]
    [EvalDistSemantics m] [MeasurableSpace α] (mx : ExceptT ε m α)
    [IsProbabilityMeasure 𝒟[mx]] :
    IsProbabilityMeasure ((SemanticsVia.exceptT ε m).evalDist mx) := sorry

end SemanticsVia
