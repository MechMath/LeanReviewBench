module

public import Batteries.Control.AlternativeMonad
public import Batteries.Control.Lemmas
public import Batteries.Control.OptionT
public import Batteries.Tactic.Lint
public import Batteries.Tactic.Lint.Basic
public import Cslib.Foundations.Control.Monad.Free
public import Cslib.Foundations.Control.Monad.IsMonadHom
public import Cslib.Foundations.Control.Monad.IsMonadHom.List
public import Cslib.Foundations.Data.PFunctor.Free
public import Cslib.Init
public import Init.Data.UInt.Lemmas
public import Lean.PrettyPrinter.Delaborator.Basic
public import Lean.PrettyPrinter.Formatter
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.Algebra.Tropical.Basic
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Control.Basic
public import Mathlib.Control.Monad.Basic
public import Mathlib.Control.Monad.Writer
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.FinEnum
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.FunLike.IsApply
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Sym
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Functor
public import Mathlib.Data.Vector.Basic
public import Mathlib.Data.Vector.Defs
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Defs
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.MeasureTheory.Measure.Comap
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Probability.UniformOn
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Tactic.Attr.Register
public import Mathlib.Tactic.Cases
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.EMetricSpace.Weak
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Util.Notation3
public import Std.Internal.ForIn
public import dep.ArkLib.Commitments.Functional.KZG.Algebra
public import dep.ArkLib.Commitments.Functional.KZG.Sampling
public import dep.ArkLib.Data.GroupTheory.PrimeOrder
public import dep.CompPoly.Data.Array.Lemmas
public import dep.CompPoly.Univariate.Basic
public import dep.CompPoly.Univariate.Linear
public import dep.CompPoly.Univariate.Raw.Core
public import dep.CompPoly.Univariate.Raw.Division
public import dep.CompPoly.Univariate.Raw.Ops
public import dep.CompPoly.Univariate.Raw.Proofs
public import dep.CompPoly.Univariate.ToPoly.Core
public import dep.PolyFun.Control.Monad.Hom
public import dep.PolyFun.Control.Monad.Support
public import dep.PolyFun.Control.Monad.Support.Instances
public import dep.PolyFun.Control.Trace
public import dep.PolyFun.PFunctor.Basic
public import dep.PolyFun.PFunctor.Bound
public import dep.PolyFun.PFunctor.Chart.Basic
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
public import dep.PolyFun.PFunctor.Trace
public import dep.ToCslib.Data.PFunctor.Free.Basic
public import dep.ToMathlib.Control.OptionT
public import dep.ToMathlib.Control.WriterT
public import dep.ToMathlib.Data.FinEnum
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
public import dep.VCVio.EvalDist.EvalDistEq
public import dep.VCVio.EvalDist.PFunctorMeasure.Core
public import dep.VCVio.EvalDist.ProbabilityNotation
public import dep.VCVio.EvalDist.ProbabilityNotation.Attr
public import dep.VCVio.OracleComp.Coercions.Add.Basic
public import dep.VCVio.OracleComp.Coercions.SubSpec.Basic
public import dep.VCVio.OracleComp.Constructions.SampleableType.Basic
public import dep.VCVio.OracleComp.EvalDist.AnswerMeasure
public import dep.VCVio.OracleComp.HasQuery.Basic
public import dep.VCVio.OracleComp.OracleComp
public import dep.VCVio.OracleComp.OracleQuery
public import dep.VCVio.OracleComp.OracleSpec
public import dep.VCVio.OracleComp.ProbComp.Basic
public import dep.VCVio.OracleComp.ProbCompLift
public import dep.VCVio.OracleComp.QueryTracking.CachingOracle
public import dep.VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import dep.VCVio.OracleComp.QueryTracking.Structures
public import dep.VCVio.OracleComp.SimSemantics.Append.Core
public import dep.VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import dep.VCVio.OracleComp.SimSemantics.SimulateQ
public import dep.VCVio.OracleComp.SimSemantics.StateT.PreservesInv
public import dep.VCVio.OracleComp.Support
public import dep.dep.CslibCompat.Basic
public import dep.dep.CslibCompat.Free

@[expose] public section

open OracleSpec OracleComp SubSpec

open CompPoly.CPolynomial

open Polynomial

open scoped NNReal ENNReal

namespace Groups

section PrimeOrder

variable {G : Type} [Group G] {p : outParam ℕ} [Fact (Nat.Prime p)]
  [PrimeOrderWith G p]

variable {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}

/-- A `t`-SDH adversary returns a challenge offset and a group element upon receiving the SRS. -/
abbrev tSdhAdversary (D : ℕ) :=
  Vector G₁ (D + 1) × Vector G₂ 2 →
    StateT unifSpec.QueryCache ProbComp (Option (ZMod p × G₁))

/-- t-SDH condition for an adversary to win. -/
abbrev tSdhCondition {g₁ : G₁} : (ZMod p × ZMod p × G₁) → Prop :=
  fun (τ, c, h) =>
    τ + c ≠ 0 ∧ h = g₁ ^ (1 / (τ + c)).val

/-- The t-SDH game for a specific adversary. -/
abbrev tSdhGame [∀ i, SampleableType (unifSpec.Range i)]
    {g₁ : G₁} {g₂ : G₂} (D : ℕ)
    (adversary : tSdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p)) :
    OptionT ProbComp (ZMod p × ZMod p × G₁) :=
  OptionT.mk (do
    let τ ← sampleNonzeroZMod (p := p)
    let srs := Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ
    let result ← (adversary srs).run' ∅
    pure (result.map (fun ((c, h) : ZMod p × G₁) =>
      (τ, c, h))))

/-- The probability of breaking `t`-SDH for a specific adversary. -/
noncomputable def tSdhExperiment [∀ i, SampleableType (unifSpec.Range i)]
    {g₁ : G₁} {g₂ : G₂} (D : ℕ)
    (adversary : tSdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p)) : ℝ≥0∞ :=
  Pr{let result ← (tSdhGame (g₁ := g₁) (g₂ := g₂) D adversary)}[(tSdhCondition (g₁ := g₁)) result]

/-- The `t`-SDH assumption bounds the success probability of every adversary in `Adv` by `error`.

For `Adv = Set.univ` and a nontrivial verifier generator, this is false below error `1`: the
trapdoor is a classical function of the verifier SRS. A meaningful instance must restrict `Adv`,
for example to generic or algebraic group adversaries, or resource-bounded adversaries. -/
def tSdhAssumption [∀ i, SampleableType (unifSpec.Range i)]
    {g₁ : G₁} {g₂ : G₂} (D : ℕ)
    (Adv : Set (tSdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p))) (error : ℝ≥0) : Prop :=
  ∀ adversary ∈ Adv,
    tSdhExperiment (g₁ := g₁) (g₂ := g₂) D adversary ≤ (error : ℝ≥0∞)

end PrimeOrder

end Groups
