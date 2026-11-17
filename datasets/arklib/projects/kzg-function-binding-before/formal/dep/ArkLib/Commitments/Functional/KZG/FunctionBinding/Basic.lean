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
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Algebra.Polynomial.Div
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
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Sym
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Data.Rat.Star
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Functor
public import Mathlib.Data.Vector.Basic
public import Mathlib.Data.Vector.Defs
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Init
public import Mathlib.LinearAlgebra.Lagrange
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
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.UniformOn
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Attr.Register
public import Mathlib.Tactic.Cases
public import Mathlib.Tactic.DepRewrite
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.EMetricSpace.Weak
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Util.Notation3
public import Std.Internal.ForIn
public import dep.ArkLib.Commitments.Functional.Basic
public import dep.ArkLib.Commitments.Functional.KZG.Algebra
public import dep.ArkLib.Commitments.Functional.KZG.Basic
public import dep.ArkLib.Commitments.Functional.KZG.Correctness
public import dep.ArkLib.Commitments.Functional.KZG.FunctionBinding.DegreeConflict
public import dep.ArkLib.Commitments.Functional.KZG.FunctionBinding.EvaluationBindingConflict
public import dep.ArkLib.Commitments.Functional.KZG.FunctionBinding.Support
public import dep.ArkLib.Commitments.Functional.KZG.FunctionBinding.TauInQueries
public import dep.ArkLib.Commitments.Functional.KZG.HardnessAssumptions
public import dep.ArkLib.Commitments.Functional.KZG.Sampling
public import dep.ArkLib.Data.Classes.Slice
public import dep.ArkLib.Data.Fin.Fold
public import dep.ArkLib.Data.Fin.Sigma
public import dep.ArkLib.Data.Fin.Tuple.Defs
public import dep.ArkLib.Data.Fin.Tuple.Lemmas
public import dep.ArkLib.Data.Fin.Tuple.Notation
public import dep.ArkLib.Data.GroupTheory.PrimeOrder
public import dep.ArkLib.OracleReduction.Basic
public import dep.ArkLib.OracleReduction.Execution
public import dep.ArkLib.OracleReduction.OracleInterface
public import dep.ArkLib.OracleReduction.Prelude
public import dep.ArkLib.OracleReduction.ProtocolSpec.Basic
public import dep.ArkLib.OracleReduction.ProtocolSpec.Cast
public import dep.ArkLib.OracleReduction.ProtocolSpec.SeqCompose
public import dep.ArkLib.OracleReduction.Security.Basic
public import dep.CompPoly.Data.Array.Lemmas
public import dep.CompPoly.Data.Classes.DCast
public import dep.CompPoly.Data.MvPolynomial.Notation
public import dep.CompPoly.ToMathlib.Finsupp.Fin
public import dep.CompPoly.ToMathlib.MvPolynomial.Equiv
public import dep.CompPoly.Univariate.Basic
public import dep.CompPoly.Univariate.Lagrange
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
public import dep.VCVio.EvalDist.Defs.Semantics.Core
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
public import dep.VCVio.OracleComp.ProbCompLift
public import dep.VCVio.OracleComp.QueryTracking.CachingOracle
public import dep.VCVio.OracleComp.QueryTracking.RandomOracle.Basic
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

open CompPoly CompPoly.CPolynomial

namespace KZG

variable {G : Type} [Group G] {p : outParam ℕ} [hp : Fact (Nat.Prime p)]
  [PrimeOrderWith G p] {g : G}

variable {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [DecidableEq G₁] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}
  {Gₜ : Type} [Group Gₜ] [PrimeOrderWith Gₜ p] [DecidableEq Gₜ]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  (pairing : (Additive G₁) →ₗ[ZMod p] (Additive G₂) →ₗ[ZMod p] (Additive Gₜ))

variable {n : ℕ}

open Commitment

/-- Local oracle interface for evaluating coefficient vectors as computable polynomials. -/
local instance functionBindingOracleInterface : OracleInterface (Fin (n + 1) → ZMod p) where
  Query := ZMod p
  toOC.spec := ZMod p →ₒ ZMod p
  toOC.impl z := do return (CPolynomial.ofFn (← read)).eval z

open scoped NNReal

namespace CommitmentScheme

open OracleSpec _root_.OracleComp SubSpec ProtocolSpec

section FunctionBinding

/-- Steps 3 and 4 of the ARSDH reduction from [CGKY25]. -/
def mapFunctionBindingInstanceToArsdhInstAux {L : ℕ} (hn : 1 ≤ n)
    (val : (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
      (Fin L → ZMod p) × (Fin L → ZMod p) × (Fin L → Bool) × (Fin L → G₁)) :
    Option (Finset (ZMod p) × G₁ × G₁) :=
  do
  let tr := FunctionBindingExtTranscript.ofTuple (p := p) val
  if let some (i₁, i₂) := findConflict tr.queryOf tr.responseOf then
    -- step 3
    return (conflictingEvaluationsArsdhOutput hn tr i₁ i₂).toTuple
  else if -- additional subcase (not in the paper): find τ in queries
    let some α₁ := (List.finRange L).findSome? fun i =>
      if tr.srs.1[0] ^ (tr.queryOf i).val == tr.srs.1[1]'(Nat.lt_add_of_pos_left hn)
      then some (tr.queryOf i) else none
  then
    -- α₁ = τ
    return (queryEqTauArsdhOutput n α₁ tr.srs).toTuple
    -- h₂ = h₁ ^ (1 / Zₛ.eval τ).val with h₁:= g₁
  else
      -- step 4
    let R := queryReps tr.queryOf
    let A ← findA R (n + 1) tr.queryOf tr.responseOf
    let S ← findS n A tr.cm tr.srs tr.queryOf tr.responseOf
    return (interpolationArsdhOutput S tr).toTuple

/-- Totalized version of `mapFunctionBindingInstanceToArsdhInstAux`, defaulting outside the
event. -/
def mapFunctionBindingInstanceToArsdhInst {L : ℕ} (hn : 1 ≤ n)
    (val : (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
      (Fin L → ZMod p) × (Fin L → ZMod p) × (Fin L → Bool) × (Fin L → G₁)) :
    (Finset (ZMod p) × G₁ × G₁) :=
  -- For instances that break function binding, the auxiliary map should always return `some`.
  Option.getD (mapFunctionBindingInstanceToArsdhInstAux hn val) (∅, 1, 1)

/-- Abbreviation for a function binding adversary for KZG. -/
abbrev KzgFunctionBindingAdversary (p : ℕ) [Fact (Nat.Prime p)] (G₁ G₂ : Type) [Group G₁]
    [PrimeOrderWith G₁ p] [Group G₂] [PrimeOrderWith G₂ p] (n : ℕ) {ι : Type}
    (oSpec : OracleSpec ι) (L : ℕ) (AuxState : Type) :=
  Commitment.FunctionBindingAdversary oSpec (Fin (n + 1) → ZMod p) G₁ AuxState L
    ⟨!v[.P_to_V], !v[G₁]⟩ (Vector G₁ (n + 1) × Vector G₂ 2)

include g₁ g₂ pairing in
/-- The reduction breaking ARSDH using a successful function-binding adversary.

The reduction follows the proof of Lemma 9.1, under Definition 9.6, in [CGKY25]. -/
def reduction (L : ℕ) (hn : 1 ≤ n) (AuxState : Type)
    (adversary : KzgFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState) :
    Groups.arsdhAdversary n (G₁ := G₁) (G₂ := G₂) (p := p) :=
    fun srs =>
    letI kzgScheme := kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
    -- designed such that ProbEvent_comp can be applied and thus the main task of reasoning
    -- is discharged to the predicate level.
    -- The auxiliary map (steps 3 and 4 of the reduction) is applied to the adversary result
    -- from steps 1 and 2.
    letI so : QueryImpl _ (StateT unifSpec.QueryCache ProbComp) :=
      QueryImpl.addLift
        (randomOracle : QueryImpl unifSpec (StateT unifSpec.QueryCache ProbComp))
        (challengeQueryImpl (pSpec := ⟨!v[.P_to_V], !v[G₁]⟩))
    (simulateQ so
          (do
            let (ck, vk) := (srs, srs)
            let claimResult ←
              liftComp (adversary.claim ck) _
            let cm := claimResult.1
            let queryOf := claimResult.2.1
            let responseOf := claimResult.2.2.1
            let stateOf := claimResult.2.2.2
            let reduction := Reduction.mk (adversary.prover ck)
              (kzgScheme.opening (ck, vk)).verifier
            let (resultPairs : Option (Fin L → Bool × G₁)) ← reduction.allOutputs
              (fun ((transcript_data, verifier_accept) :
                (FullTranscript ⟨!v[.P_to_V], !v[G₁]⟩ × Bool × Unit) × Bool) =>
                (verifier_accept, transcript_data.1 0))
              (fun i => (cm, (⟨queryOf i, responseOf i⟩ :
                (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
                  OracleInterface.Response q))) stateOf
            return resultPairs.map (fun resultOf =>
              let accepts : Fin L → Bool := fun i => (resultOf i).1
              let proofs : Fin L → G₁ := fun i => (resultOf i).2
              mapFunctionBindingInstanceToArsdhInst hn
                (srs, cm, queryOf, responseOf, accepts, proofs))
          ))

omit [DecidableEq G₁] in
/-- The KZG scheme satisfies function binding provided ARSDH holds. -/
theorem function_binding {g₁ : G₁} {g₂ : G₂}
    (L : ℕ) (hn : 1 ≤ n) (hp : p ≥ n + 2) (hg₁ : g₁ ≠ 1)
    (hpair : pairing g₁ g₂ ≠ 0)
    [SampleableType G₁] (arsdhError : ℝ≥0)
    (hArsdh : Groups.arsdhAssumption (G₁ := G₁) (G₂ := G₂) (g₁ := g₁) (g₂ := g₂)
     n arsdhError) :
    Commitment.functionBinding (L := L) (init := pure ∅) (impl := randomOracle)
      (hn := rfl)
      (kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)) arsdhError := sorry

end FunctionBinding

end CommitmentScheme

end KZG
