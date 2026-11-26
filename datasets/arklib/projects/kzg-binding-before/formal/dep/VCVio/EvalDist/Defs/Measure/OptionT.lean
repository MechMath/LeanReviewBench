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
public import dep.ToMathlib.Data.Vector.Induction
public import dep.ToMathlib.MeasureTheory.MeasurableSpace.Option
public import dep.ToMathlib.MeasureTheory.Measure.Option
public import dep.ToMathlib.MeasureTheory.Measure.Subprobability
public import dep.VCVio.EvalDist.Defs.Measure.Core
public import dep.VCVio.EvalDist.Defs.Measure.Failure

public section

open MeasureTheory

universe u v

/-- Interpret successful `OptionT` results by pulling the run measure back along `some`. -/
noncomputable instance (priority := 20) instEvalDistSemanticsOptionT
    {m : Type u → Type v} [EvalDistSemantics m] :
    EvalDistSemantics (OptionT m) where
  denote mx := (𝒟[mx.run]).comap some
  apply_univ_le_one mx :=
    calc
      (𝒟[mx.run]).comap some Set.univ = 𝒟[mx.run] (some '' Set.univ) :=
        Option.measurableEmbedding_some.comap_apply _ _
      _ ≤ 𝒟[mx.run] Set.univ := measure_mono (Set.subset_univ _)
      _ ≤ 1 := evalDist_apply_univ_le_one mx.run

/-- Optional semantics preserves pure whenever the base semantics does. -/
instance (priority := 20) instLawfulPureEvalDistSemanticsOptionT
    {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
    [LawfulPureEvalDistSemantics m] : LawfulPureEvalDistSemantics (OptionT m) := sorry

/-- Optional failure has zero measure whenever the base semantics preserves pure. -/
instance (priority := 20) instLawfulFailureEvalDistSemanticsOptionT
    {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
    [LawfulPureEvalDistSemantics m] : LawfulFailureEvalDistSemantics (OptionT m) := sorry

/-- Lifting a lossless computation into the optional monad preserves its probability measure. -/
instance OptionT.isProbabilityMeasure_evalDist_lift
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : m α) [IsProbabilityMeasure 𝒟[mx]] :
    IsProbabilityMeasure 𝒟[OptionT.lift mx] := sorry

/-- A monadic lift into the optional monad preserves a known probability measure. -/
instance OptionT.isProbabilityMeasure_evalDist_liftM
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : m α) [IsProbabilityMeasure 𝒟[mx]] :
    IsProbabilityMeasure 𝒟[(liftM mx : OptionT m α)] := sorry

/-- A measurable map of successful optional results is the measure pushforward. -/
theorem OptionT.evalDist_map
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (mx : OptionT m α) (f : α → β) (hf : Measurable f) :
    𝒟[f <$> mx] = 𝒟[mx].map f := sorry

/-- Optional semantics satisfies the measurable-bind law for successful-output families. The
full-run observer refines the source space, whose identity map transports the source measure. -/
instance (priority := 20) instLawfulEvalDistSemanticsOptionT
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] :
    LawfulEvalDistSemantics (OptionT m) := sorry
