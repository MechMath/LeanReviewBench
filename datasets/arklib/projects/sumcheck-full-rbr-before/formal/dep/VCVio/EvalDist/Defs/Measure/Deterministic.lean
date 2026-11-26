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
public import Mathlib.Init
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
public import dep.VCVio.EvalDist.Defs.Measure.Failure
public import dep.VCVio.EvalDist.ProbabilityNotation
public import dep.VCVio.EvalDist.ProbabilityNotation.Attr

public section

open MeasureTheory

universe u v

/-- A deterministic total computation denotes its Dirac output measure. -/
noncomputable instance (priority := 20) instEvalDistSemanticsId : EvalDistSemantics Id where
  denote mx := Measure.dirac mx.run
  apply_univ_le_one _ := sorry

/-- Every deterministic total computation denotes a probability measure. -/
instance Id.isProbabilityMeasure_evalDist {α : Type u} [MeasurableSpace α] (mx : Id α) :
    IsProbabilityMeasure 𝒟[mx] := sorry

/-- Deterministic total computations respect the measurable Giry laws. -/
instance (priority := 20) instLawfulEvalDistSemanticsId : LawfulEvalDistSemantics Id := sorry

/-- A deterministic optional result denotes zero on failure and a Dirac measure on success. -/
noncomputable instance (priority := 20) instEvalDistSemanticsOption :
    EvalDistSemantics Option where
  denote mx := mx.elim 0 Measure.dirac
  apply_univ_le_one mx := sorry

/-- Deterministic optional failure has zero successful-output measure. -/
instance (priority := 20) instLawfulFailureEvalDistSemanticsOption :
    LawfulFailureEvalDistSemantics Option := sorry

/-- A present optional result denotes a probability measure. -/
instance Option.isProbabilityMeasure_evalDist_some {α : Type u} [MeasurableSpace α] (x : α) :
    IsProbabilityMeasure 𝒟[(some x : Option α)] := sorry

/-- Deterministic optional computations respect the measurable Giry laws. -/
instance (priority := 20) instLawfulEvalDistSemanticsOption :
    LawfulEvalDistSemantics Option := sorry

/-- A deterministic exceptional result assigns mass only to its successful output. -/
noncomputable instance (priority := 20) instEvalDistSemanticsExcept {ε : Type u} :
    EvalDistSemantics (Except ε) where
  denote mx := match mx with
    | .error _ => 0
    | .ok x => Measure.dirac x
  apply_univ_le_one mx := sorry

/-- A successful exceptional result denotes a probability measure. -/
instance Except.isProbabilityMeasure_evalDist_ok {ε : Type u} {α : Type v}
    [MeasurableSpace α] (x : α) :
    IsProbabilityMeasure 𝒟[(Except.ok x : Except ε α)] := sorry

/-- Deterministic exceptional computations respect the measurable Giry laws. -/
instance (priority := 20) instLawfulEvalDistSemanticsExcept {ε : Type u} :
    LawfulEvalDistSemantics (Except ε) := sorry
