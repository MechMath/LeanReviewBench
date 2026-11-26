module

public import Batteries.Tactic.Lint
public import Batteries.Tactic.Lint.Basic
public import Cslib.Foundations.Data.PFunctor.Free
public import Cslib.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
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
public import dep.VCVio.EvalDist.PFunctorMeasure.Core
public import dep.VCVio.OracleComp.HasQuery.Basic
public import dep.VCVio.OracleComp.OracleComp
public import dep.VCVio.OracleComp.OracleQuery
public import dep.VCVio.OracleComp.OracleSpec
public import dep.dep.CslibCompat.Basic
public import dep.dep.CslibCompat.Free

public section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

universe u v

namespace OracleSpec

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}

/-- A probability measure on the answers to each query of an oracle specification.

Oracle answers carry the discrete measurable structure, so a chosen measure is determined by the
mass of single answers and no measurable-space arguments appear on answer types. Answer types
with another measurable structure are modeled by `PFunctor.AnswerMeasure` on the underlying
polynomial functor. -/
abbrev AnswerMeasure (spec : OracleSpec.{u, v} ι) :=
  @PFunctor.AnswerMeasure spec.toPFunctor fun _ ↦ ⊤

namespace AnswerMeasure

/-- The probability measure assigned to the answer of query `t`. -/
abbrev toMeasure [AnswerMeasure spec] (t : spec.Domain) : @Measure (spec.Range t) ⊤ :=
  @PFunctor.AnswerMeasure.toMeasure spec.toPFunctor (fun _ ↦ ⊤) _ t

/-- Each answer measure is a probability measure. This restates the polynomial-functor instance at
the oracle API, whose answer types are `spec.Range t` rather than `spec.toPFunctor.B t`, so that
instance search finds it for oracle goals. -/
instance isProbabilityMeasure_toMeasure [AnswerMeasure spec] (t : spec.Domain) :
    @IsProbabilityMeasure (spec.Range t) ⊤ (toMeasure t) := sorry

end AnswerMeasure

/-- Combining specifications combines their answer measures. -/
@[reducible]
noncomputable instance AnswerMeasure.add {ι' : Type*} (spec' : OracleSpec.{_, v} ι')
    [AnswerMeasure spec] [AnswerMeasure spec'] : AnswerMeasure (spec + spec') :=
  @PFunctor.AnswerMeasure.mk (spec + spec').toPFunctor (fun _ ↦ ⊤)
    (fun
      | .inl t => AnswerMeasure.toMeasure t
      | .inr t => AnswerMeasure.toMeasure t)
    (fun
      | .inl t => AnswerMeasure.isProbabilityMeasure_toMeasure t
      | .inr t => AnswerMeasure.isProbabilityMeasure_toMeasure t)

/-- A chosen measure interpretation that samples uniformly from each answer type.

It extends the choice of answer measures with the law that each one is the uniform measure on
its answer type, and carries no finiteness or inhabitedness data. `uniformOn Set.univ` is a
probability measure exactly on a finite, nonempty type, which
`AnswerMeasure.isProbabilityMeasure` records, so `UniformAnswerMeasure.finite_range` and
`UniformAnswerMeasure.nonempty_range` recover both facts. Statements about cardinalities take
`[Fintype (spec.Range t)]` for the queries they mention. -/
class UniformAnswerMeasure (spec : OracleSpec.{u, v} ι) extends AnswerMeasure spec where
  /-- Each query uses the uniform probability measure on its answer type. -/
  toMeasure_eq_uniform : ∀ t, toMeasure t = @uniformOn (spec.Range t) ⊤ Set.univ

attribute [simp] UniformAnswerMeasure.toMeasure_eq_uniform

/-- The answer measure exposed by the oracle API is uniform for a uniform specification. -/
theorem AnswerMeasure.toMeasure_eq_uniformOn [UniformAnswerMeasure spec] (t : spec.Domain) :
    toMeasure t = @uniformOn (spec.Range t) ⊤ Set.univ := sorry

/-- Select uniform measure semantics for an oracle specification whose answer types are finite
and nonempty. -/
@[expose, reducible]
noncomputable def UniformAnswerMeasure.ofFiniteNonempty (spec : OracleSpec.{u, v} ι)
    [∀ t, Finite (spec.Range t)] [∀ t, Nonempty (spec.Range t)] : UniformAnswerMeasure spec where
  toMeasure _ := @uniformOn _ ⊤ Set.univ
  isProbabilityMeasure t :=
    letI : MeasurableSpace (spec.Range t) := ⊤
    inferInstance
  toMeasure_eq_uniform _ := rfl

/-- Uniform measure semantics for the finite-range selection oracle. -/
@[reducible]
noncomputable def UniformAnswerMeasure.unifSpec : UniformAnswerMeasure _root_.unifSpec :=
  ofFiniteNonempty _

/-- Uniform measure semantics for the fair-coin oracle. -/
@[reducible]
noncomputable def UniformAnswerMeasure.coinSpec : UniformAnswerMeasure _root_.coinSpec :=
  ofFiniteNonempty _

attribute [instance] UniformAnswerMeasure.unifSpec UniformAnswerMeasure.coinSpec

namespace UniformAnswerMeasure

variable [UniformAnswerMeasure spec]

end UniformAnswerMeasure

/-- Combining uniform specifications preserves each configured answer measure. -/
@[reducible]
noncomputable instance UniformAnswerMeasure.add {ι' : Type*} (spec' : OracleSpec.{_, v} ι')
    [UniformAnswerMeasure spec] [UniformAnswerMeasure spec'] :
    UniformAnswerMeasure (spec + spec') where
  toAnswerMeasure := AnswerMeasure.add spec'
  toMeasure_eq_uniform
    | .inl t => AnswerMeasure.toMeasure_eq_uniformOn (spec := spec) t
    | .inr t => AnswerMeasure.toMeasure_eq_uniformOn (spec := spec') t

end OracleSpec

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}

/-- Oracle computations denote the measure fold of their chosen answer measures. -/
noncomputable instance (priority := 30) instEvalDistSemantics [OracleSpec.AnswerMeasure spec] :
    EvalDistSemantics (OracleComp spec) :=
  letI : ∀ a, MeasurableSpace (spec.toPFunctor.B a) := fun _ ↦ ⊤
  PFunctor.FreeM.instEvalDistSemanticsFreeM

/-- Oracle computations denote `pure` as a Dirac measure. -/
noncomputable instance (priority := 30) instLawfulPureEvalDistSemantics
    [OracleSpec.AnswerMeasure spec] : LawfulPureEvalDistSemantics (OracleComp spec) := sorry

/-- Over discrete oracle answers, the measure semantics satisfies the Giry monad laws. -/
noncomputable instance (priority := 30) instLawfulEvalDistSemantics
    [OracleSpec.AnswerMeasure spec] : LawfulEvalDistSemantics (OracleComp spec) := sorry

end OracleComp
