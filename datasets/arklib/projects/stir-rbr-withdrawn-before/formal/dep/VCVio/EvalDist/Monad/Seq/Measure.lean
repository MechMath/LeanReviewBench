module

public import Batteries.Tactic.Lint.Basic
public import Lean.PrettyPrinter.Delaborator.Basic
public import Lean.PrettyPrinter.Formatter
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
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic.Attr.Register
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.EMetricSpace.Weak
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import dep.ToMathlib.Data.Vector.Induction
public import dep.ToMathlib.MeasureTheory.Measure.Subprobability
public import dep.VCVio.EvalDist.Defs.Measure.Core
public import dep.VCVio.EvalDist.ProbabilityNotation
public import dep.VCVio.EvalDist.ProbabilityNotation.Attr

public section

open MeasureTheory

universe u v

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β γ : Type u}

section

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

end

section

variable [MeasurableSpace β] [MeasurableSpace γ]

end

section

variable [MeasurableSpace α] [MeasurableSpace γ]

end

section

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- An independent applicative pair inherits losslessness from its factors. -/
instance evalDist.instIsProbabilityMeasureSeqMapProdMk (mx : m α) (my : m β)
    [IsProbabilityMeasure 𝒟[mx]] [IsProbabilityMeasure 𝒟[my]] :
    IsProbabilityMeasure 𝒟[Prod.mk <$> mx <*> my] := sorry

/-- Keeping the first of two lossless computations preserves its probability certificate. -/
instance evalDist.instIsProbabilityMeasureSeqLeft (mx : m α) (my : m β)
    [IsProbabilityMeasure 𝒟[mx]] [IsProbabilityMeasure 𝒟[my]] :
    IsProbabilityMeasure 𝒟[mx <* my] := sorry

/-- Keeping the second of two lossless computations preserves its probability certificate. -/
instance evalDist.instIsProbabilityMeasureSeqRight (mx : m α) (my : m β)
    [IsProbabilityMeasure 𝒟[mx]] [IsProbabilityMeasure 𝒟[my]] :
    IsProbabilityMeasure 𝒟[mx *> my] := sorry

end

section events

universe v'

variable {m : Type → Type v'} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β : Type}

end events
