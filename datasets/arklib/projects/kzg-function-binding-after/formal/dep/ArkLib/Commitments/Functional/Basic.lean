module

public import Batteries.Control.AlternativeMonad
public import Batteries.Control.Lemmas
public import Batteries.Control.OptionT
public import Batteries.Data.Fin.Fold
public import Batteries.Data.Vector.Lemmas
public import Batteries.Tactic.Lint
public import Batteries.Tactic.Lint.Basic
public import Cslib.Foundations.Control.Monad.Free
public import Cslib.Foundations.Control.Monad.IsMonadHom
public import Cslib.Foundations.Control.Monad.IsMonadHom.List
public import Cslib.Foundations.Data.PFunctor.Free
public import Cslib.Init
public import Init.Data.UInt.Lemmas
public import Init.Data.Vector.Lemmas
public import Lean.PrettyPrinter.Delaborator.Basic
public import Lean.PrettyPrinter.Formatter
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Finsupp.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Control.Basic
public import Mathlib.Control.Monad.Basic
public import Mathlib.Control.Monad.Writer
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fin.Tuple.Take
public import Mathlib.Data.FinEnum
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finsupp.Fin
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.FunLike.IsApply
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Sym
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Data.Rat.Star
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Functor
public import Mathlib.Data.Vector.Basic
public import Mathlib.Data.Vector.Defs
public import Mathlib.Init
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Equiv.Bool
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
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.UniformOn
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Attr.Register
public import Mathlib.Tactic.DepRewrite
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.EMetricSpace.Weak
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Util.Notation3
public import Std.Internal.ForIn
public import dep.ArkLib.Data.Classes.Slice
public import dep.ArkLib.Data.Fin.Fold
public import dep.ArkLib.Data.Fin.Sigma
public import dep.ArkLib.Data.Fin.Tuple.Defs
public import dep.ArkLib.Data.Fin.Tuple.Lemmas
public import dep.ArkLib.Data.Fin.Tuple.Notation
public import dep.ArkLib.OracleReduction.Basic
public import dep.ArkLib.OracleReduction.Execution
public import dep.ArkLib.OracleReduction.OracleInterface
public import dep.ArkLib.OracleReduction.Prelude
public import dep.ArkLib.OracleReduction.ProtocolSpec.Basic
public import dep.ArkLib.OracleReduction.ProtocolSpec.Cast
public import dep.ArkLib.OracleReduction.ProtocolSpec.SeqCompose
public import dep.ArkLib.OracleReduction.Security.Basic
public import dep.CompPoly.Data.Classes.DCast
public import dep.CompPoly.Data.MvPolynomial.Notation
public import dep.CompPoly.ToMathlib.Finsupp.Fin
public import dep.CompPoly.ToMathlib.MvPolynomial.Equiv
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
public import dep.PolyFun.PFunctor.Free.Path.Execution
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
public import dep.VCVio.EvalDist.Defs.Support
public import dep.VCVio.EvalDist.EvalDistEq
public import dep.VCVio.EvalDist.Instances.OptionT
public import dep.VCVio.EvalDist.PFunctorMeasure.Core
public import dep.VCVio.EvalDist.ProbabilityNotation
public import dep.VCVio.EvalDist.ProbabilityNotation.Attr
public import dep.VCVio.OracleComp.Coercions.Add.Basic
public import dep.VCVio.OracleComp.Coercions.SubSpec.Basic
public import dep.VCVio.OracleComp.Constructions.Replicate.Basic
public import dep.VCVio.OracleComp.Constructions.SampleableType.Basic
public import dep.VCVio.OracleComp.EvalDist.AnswerMeasure
public import dep.VCVio.OracleComp.HasQuery.Basic
public import dep.VCVio.OracleComp.OracleComp
public import dep.VCVio.OracleComp.OracleContext
public import dep.VCVio.OracleComp.OracleQuery
public import dep.VCVio.OracleComp.OracleSpec
public import dep.VCVio.OracleComp.ProbComp.Basic
public import dep.VCVio.OracleComp.QueryTracking.Structures
public import dep.VCVio.OracleComp.SimSemantics.Append.Core
public import dep.VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import dep.VCVio.OracleComp.SimSemantics.ReaderT.Basic
public import dep.VCVio.OracleComp.SimSemantics.SimulateQ
public import dep.VCVio.OracleComp.SimSemantics.StateT.PreservesInv
public import dep.VCVio.OracleComp.Support
public import dep.dep.CslibCompat.Basic
public import dep.dep.CslibCompat.Free

@[expose] public section

namespace Commitment

open OracleSpec OracleComp SubSpec ProtocolSpec

variable {ι : Type} (oSpec : OracleSpec ι) (Data Commitment Decommitment ComKey VerifKey : Type)

/-- Key generation for a commitment scheme, producing a committer key and a verifier key. -/
structure KeyGen where
  keygen : OracleComp oSpec (ComKey × VerifKey)

/-- The commitment algorithm, parameterized by the committer key and the data to commit. -/
structure Commit where
  commit : ComKey → Data → OracleComp oSpec (Commitment × Decommitment)

variable [O : OracleInterface Data] {n : ℕ} (pSpec : ProtocolSpec n)

/-- The opening protocol used to prove a claimed oracle response for committed data. -/
structure Opening where
  opening : (ComKey × VerifKey) →
    Proof oSpec (Commitment × (q : O.Query) × O.Response q) (Data × Decommitment) pSpec

/-- A commitment scheme with key generation, commitment, and opening algorithms. -/
structure Scheme extends
    KeyGen oSpec ComKey VerifKey,
    Commit oSpec Data Commitment Decommitment ComKey,
    Opening oSpec Data Commitment Decommitment ComKey VerifKey pSpec

section Security

noncomputable section

open scoped NNReal ENNReal

variable [DecidableEq ι]
  {oSpec : OracleSpec ι} {Data : Type} [O : OracleInterface Data]
  {Commitment Decommitment ComKey VerifKey : Type} [∀ t, Fintype (oSpec.Range t)] {n : ℕ}
  {pSpec : ProtocolSpec n} [∀ t, Inhabited ([pSpec.Challenge]ₒ.Range t)]
  [∀ t, Fintype ([pSpec.Challenge]ₒ.Range t)]
  [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (scheme : Scheme oSpec Data Commitment Decommitment ComKey VerifKey pSpec)

/-- An adversary in the function binding game returns a commitment `cm`, and for each index in
  `Fin L`, a query, a claimed response to the query, and an auxiliary private state (to be passed
  to the malicious prover in the opening procedure). -/
structure FunctionBindingAdversary (oSpec : OracleSpec ι) (Data Commitment AuxState : Type)
  [O : OracleInterface Data] (L : ℕ) {n : ℕ} (pSpec : ProtocolSpec n) (ComKey : Type)
where
  claim : (ComKey →
    OracleComp oSpec (Commitment ×
      (queryOf : Fin L → O.Query) ×
      ((i : Fin L) → O.Response (queryOf i)) ×
      (Fin L → AuxState)))
  prover : (ComKey →
    Prover oSpec (Commitment × (q : O.Query) × O.Response q) AuxState Bool Unit pSpec)

/-- Function binding condition for an adversary to win the function-binding game. -/
abbrev functionBindingCondition {L : ℕ} :
    ((queryOf : Fin L → O.Query) ×
      ((i : Fin L) → O.Response (queryOf i)) × (Fin L → Bool)) → Prop :=
  fun ⟨queryOf, responseOf, acceptedOf⟩ ↦
    let S : Finset (Fin L) := Finset.univ
    (∀ i ∈ S, acceptedOf i = true)
    ∧ (¬ ∃ (d : Data), ∀ i ∈ S, O.answer d (queryOf i) = responseOf i)

/-- The function-binding game for a specific adversary. -/
abbrev functionBindingGame {L : ℕ} (hn : n = 1)
    (AuxState : Type)
    [∀ i, VCVCompatible ((hn ▸ pSpec).Challenge i)]
    [∀ i, SampleableType ((hn ▸ pSpec).Challenge i)]
    (scheme : Scheme oSpec Data Commitment Decommitment ComKey VerifKey (hn ▸ pSpec))
    (adversary :
      FunctionBindingAdversary oSpec Data Commitment AuxState L (hn ▸ pSpec)
        ComKey) :
    OptionT ProbComp ((queryOf : Fin L → O.Query) ×
      ((i : Fin L) → O.Response (queryOf i)) × (Fin L → Bool)) :=
    let pImpl : QueryImpl (oSpec + [(hn ▸ pSpec).Challenge]ₒ) (StateT σ ProbComp) :=
      QueryImpl.addLift impl (challengeQueryImpl (pSpec := hn ▸ pSpec))
    OptionT.mk do
      let s ← init
      let (ck, vk) ← (simulateQ impl scheme.keygen).run' s
      (simulateQ pImpl <| (show OracleComp _ _ from do
        let ⟨cm, queryOf, responseOf, stateOf⟩ ← liftComp (adversary.claim ck) _
        let reduction := Reduction.mk (adversary.prover ck) (scheme.opening (ck, vk)).verifier
        let (accepts : Option (Fin L → Bool)) ← reduction.allVerdicts
          (fun i ↦
            (cm, (⟨queryOf i, responseOf i⟩ : (q : O.Query) × O.Response q)))
          stateOf
        pure (accepts.map fun accepts ↦ (⟨queryOf, responseOf, accepts⟩ :
          (queryOf : Fin L → O.Query) ×
            ((i : Fin L) → O.Response (queryOf i)) × (Fin L → Bool)))
      )).run' s

/-- The probability of breaking function binding for a specific adversary. -/
def functionBindingExperiment {L : ℕ} (hn : n = 1)
    (AuxState : Type)
    [∀ i, VCVCompatible ((hn ▸ pSpec).Challenge i)]
    [∀ i, SampleableType ((hn ▸ pSpec).Challenge i)]
    (scheme : Scheme oSpec Data Commitment Decommitment ComKey VerifKey (hn ▸ pSpec))
    (adversary :
      FunctionBindingAdversary oSpec Data Commitment AuxState L (hn ▸ pSpec)
        ComKey) : ℝ≥0∞ :=
    Pr{let result ← functionBindingGame init impl hn AuxState scheme adversary}[
      functionBindingCondition (Data := Data) result]

end

end Security

end Commitment
