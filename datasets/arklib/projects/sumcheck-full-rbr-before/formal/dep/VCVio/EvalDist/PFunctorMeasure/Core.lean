module

public import Batteries.Tactic.Lint
public import Batteries.Tactic.Lint.Basic
public import Cslib.Foundations.Data.PFunctor.Free
public import Cslib.Init
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
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Data.Vector.Basic
public import Mathlib.Data.Vector.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Defs
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Probability.UniformOn
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.EMetricSpace.Weak
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Util.Notation3
public import dep.PolyFun.Control.Monad.Hom
public import dep.PolyFun.PFunctor.Basic
public import dep.PolyFun.PFunctor.Equiv.Basic
public import dep.PolyFun.PFunctor.Lens.Basic
public import dep.PolyFun.PFunctor.Obj
public import dep.ToMathlib.Data.Vector.Induction
public import dep.ToMathlib.MeasureTheory.Measure.Subprobability
public import dep.VCVio.EvalDist.Defs.Measure.Core
public import dep.dep.CslibCompat.Basic
public import dep.dep.CslibCompat.Free

@[expose] public section

open MeasureTheory ProbabilityTheory

universe u v w uA

namespace PFunctor

/-- Per-operation answer measures for a polynomial interface.

The measurable structure on answer types is a separate parameter rather than a field, mirroring
Mathlib's separation of `MeasurableSpace` from the measures carried on it. Answer types need not
be discrete. -/
class AnswerMeasure (P : PFunctor.{uA, u}) [∀ a, MeasurableSpace (P.B a)] where
  /-- The distribution of answers to an operation. -/
  toMeasure : (a : P.A) → Measure (P.B a)
  /-- Answering an operation is lossless. -/
  isProbabilityMeasure : ∀ a, IsProbabilityMeasure (toMeasure a)

attribute [instance] AnswerMeasure.isProbabilityMeasure

namespace FreeM

variable {P : PFunctor.{uA, u}} [∀ a, MeasurableSpace (P.B a)] [P.AnswerMeasure]
  {α : Type v} {β : Type w}

open scoped Classical in
/-- The measure denoted by a polynomial free program. A measurable continuation uses Giry bind;
an unmeasurable continuation denotes zero. Probability-mass preservation requires measurability. -/
noncomputable def denote [MeasurableSpace α] : FreeM P α → Measure α
  | .pure x => Measure.dirac x
  | .liftBind a cont =>
      if AEMeasurable (fun b => denote (cont b)) (AnswerMeasure.toMeasure a) then
        Measure.bind (AnswerMeasure.toMeasure a) fun b => denote (cont b)
      else 0

@[simp]
theorem denote_pure [MeasurableSpace α] (x : α) :
    denote (pure x : FreeM P α) = Measure.dirac x := sorry

variable [∀ a, DiscreteMeasurableSpace (P.B a)]

/-- Every program over discrete answer types denotes a probability measure, independently of
the measurable space on its output. -/
@[instance]
theorem isProbabilityMeasure_denote [MeasurableSpace α] (program : FreeM P α) :
    IsProbabilityMeasure (denote program) := sorry

/-- `denote` preserves bind when the denoted continuation is measurable. Discrete answer types
discharge the recursive measurability obligation inside the free program. -/
theorem denote_bind [MeasurableSpace α] [MeasurableSpace β]
    (program : FreeM P α) (f : α → FreeM P β)
    (hf : Measurable fun x => denote (f x)) :
    denote (FreeM.bind program f) = Measure.bind (denote program) fun x => denote (f x) := sorry

end FreeM

namespace FreeM

variable {P : PFunctor.{uA, u}} [∀ a, MeasurableSpace (P.B a)] [P.AnswerMeasure]
  {α : Type u}

/-- Every free program denotes a subprobability measure. Measurable continuations preserve the
mass bound through integration; unmeasurable continuations have zero denotation. -/
theorem denote_apply_univ_le_one [MeasurableSpace α] (program : FreeM P α) :
    denote program Set.univ ≤ 1 := sorry

/-- The direct free-monad fold supplies measure semantics for a measure-valued specification. -/
noncomputable instance (priority := 20) instEvalDistSemanticsFreeM :
    EvalDistSemantics (FreeM P) where
  denote := denote
  apply_univ_le_one := denote_apply_univ_le_one

/-- The direct free-monad measure fold preserves pure without any discreteness assumption on
oracle answers. -/
noncomputable instance (priority := 20) instLawfulPureEvalDistSemanticsFreeM :
    LawfulPureEvalDistSemantics (FreeM P) := sorry

variable [∀ a, DiscreteMeasurableSpace (P.B a)]

instance [MeasurableSpace α] (program : FreeM P α) : IsProbabilityMeasure 𝒟[program] := sorry

/-- Over a discrete-answer interface, the direct measure semantics satisfies the Giry monad
laws. -/
noncomputable instance (priority := 20) instLawfulEvalDistSemanticsFreeM :
    LawfulEvalDistSemantics (FreeM P) := sorry

end FreeM

end PFunctor
