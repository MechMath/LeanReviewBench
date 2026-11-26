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
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Ring.Regular
public import Mathlib.Basic.Logic.Basic
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
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sets
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
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
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
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.UniformOn
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Attr.Register
public import Mathlib.Tactic.DepRewrite
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.EMetricSpace.Weak
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Util.Notation3
public import Std.Internal.ForIn
public import dep.ArkLib.Data.Classes.Slice
public import dep.ArkLib.Data.Fin.Basic
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
public import dep.ArkLib.OracleReduction.Security.RoundByRound
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
public import dep.ToMathlib.Control.OptionT
public import dep.ToMathlib.Control.WriterT
public import dep.ToMathlib.Data.FinEnum
public import dep.ToMathlib.Data.Vector.Induction
public import dep.ToMathlib.MeasureTheory.MeasurableSpace.Except
public import dep.ToMathlib.MeasureTheory.MeasurableSpace.Option
public import dep.ToMathlib.MeasureTheory.Measure.Option
public import dep.ToMathlib.MeasureTheory.Measure.Subprobability
public import dep.VCVio.EvalDist.Defs.Measure.Core
public import dep.VCVio.EvalDist.Defs.Measure.Deterministic
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
public import dep.VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import dep.VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import dep.VCVio.OracleComp.QueryTracking.Structures
public import dep.VCVio.OracleComp.QueryTracking.Tracing.Core
public import dep.VCVio.OracleComp.SimSemantics.Append.Core
public import dep.VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import dep.VCVio.OracleComp.SimSemantics.QueryImpl.Constructions.Core
public import dep.VCVio.OracleComp.SimSemantics.ReaderT.Basic
public import dep.VCVio.OracleComp.SimSemantics.SimulateQ
public import dep.VCVio.OracleComp.Support
public import dep.dep.CslibCompat.Basic
public import dep.dep.CslibCompat.Free

@[expose] public section

open OracleComp OracleSpec SubSpec

open ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- Arity bookkeeping for `Prover.append`'s state family. Stated as a standalone lemma
rather than an inline `by omega`: under the module system a tactic proof inside a public
definition is elaborated lazily, which would leave a metavariable in the type of
`sendMessage`'s `state`. -/
theorem Prover.append_state_arity (m n : ℕ) : m + n + 1 = m + 1 + n := sorry

/-- Compose two provers by feeding the first prover's output into the second prover's input.
The first prover's final state is retained until the second protocol's first round; for an empty
second protocol, the transfer occurs during output. -/
def Prover.append (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂) :
      Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂) where

  /- The combined prover's states are the concatenation of the first prover's states and the second
  prover's states (except the first one). -/
  PrvState := Fin.append (m := m + 1) P₁.PrvState (Fin.tail P₂.PrvState) ∘
    Fin.cast (Prover.append_state_arity m n)

  /- The combined prover always starts with the first prover's input function, including when the
  first protocol is empty. The second prover is initialized when the seam is processed. -/
  input := fun ctxIn => by
    simp only [Function.comp_apply, Fin.cast_zero, Fin.append_zero_of_succ_left]
    exact P₁.input ctxIn

  /- The combined prover sends messages according to the round index `i` as follows:
  - if `i < m`, then it sends the message & updates the state as the first prover
  - if `i = m`, then it runs the first prover's output, initializes the second prover from that
    output, and sends the second prover's first message
  - if `i > m`, then it sends the message & updates the state as the second prover. -/
  sendMessage := fun ⟨i, hDir⟩ state => by
    dsimp [Fin.vappend_eq_append, Fin.append, Fin.addCases, Fin.tail,
      Fin.cast, Fin.castLT, Fin.succ, Fin.castSucc] at hDir state ⊢
    by_cases hi : i < m
    · haveI : i < m + 1 := sorry
      simp only [hi, Fin.vappend_left_of_lt, Order.lt_add_one_iff, Order.add_one_le_iff,
        ↓reduceDIte] at hDir ⊢
      simp only [this, ↓reduceDIte] at state
      exact P₁.sendMessage ⟨⟨i, hi⟩, hDir⟩ state
    · by_cases hi' : i = m
      · simp only [hi', lt_self_iff_false, not_false_eq_true,
          Fin.vappend_right_of_not_lt, tsub_self,
          lt_add_iff_pos_right, Order.lt_one_iff, ↓reduceDIte, zero_add,
          eq_rec_constant] at hDir state ⊢
        exact (do
          let ctxIn₂ ← P₁.output state
          letI state₂ := P₂.input ctxIn₂
          P₂.sendMessage ⟨⟨0, sorry⟩, hDir⟩ state₂)
      · haveI hi1 : ¬ i < m + 1 := sorry
        haveI hi2 : i - (m + 1) + 1 = i - m := sorry
        simp only [hi, not_false_eq_true, Fin.vappend_right_of_not_lt,
          Order.lt_add_one_iff, Order.add_one_le_iff, ↓reduceDIte,
          Nat.reduceSubDiff, eq_rec_constant] at hDir ⊢
        simp only [hi1, ↓reduceDIte, eq_rec_constant] at state
        exact P₂.sendMessage ⟨⟨i - m, sorry⟩, hDir⟩ (dcast (sorry) state)

  /- Receiving challenges is implemented essentially the same as sending messages, modulo the
  difference in direction. -/
  receiveChallenge := fun ⟨i, hDir⟩ state => by
    dsimp [ProtocolSpec.append, Fin.append, Fin.addCases, Fin.tail,
      Fin.cast, Fin.castLT, Fin.succ, Fin.castSucc] at hDir state ⊢
    by_cases hi : i < m
    · haveI : i < m + 1 := sorry
      simp only [hi, Fin.vappend_left_of_lt, Order.lt_add_one_iff, Order.add_one_le_iff,
        ↓reduceDIte] at hDir ⊢
      simp only [this, ↓reduceDIte] at state
      exact P₁.receiveChallenge ⟨⟨i, hi⟩, hDir⟩ state
    · by_cases hi' : i = m
      · simp only [hi', lt_self_iff_false, not_false_eq_true,
          Fin.vappend_right_of_not_lt, tsub_self,
          lt_add_iff_pos_right, Order.lt_one_iff, ↓reduceDIte, zero_add,
          eq_rec_constant] at hDir state ⊢
        exact (do
          let ctxIn₂ ← P₁.output state
          letI state₂ := P₂.input ctxIn₂
          P₂.receiveChallenge ⟨⟨0, sorry⟩, hDir⟩ state₂)
      · haveI hi1 : ¬ i < m + 1 := sorry
        haveI hi2 : i - (m + 1) + 1 = i - m := sorry
        simp only [hi, not_false_eq_true, Fin.vappend_right_of_not_lt,
          Order.lt_add_one_iff, Order.add_one_le_iff, ↓reduceDIte,
          Nat.reduceSubDiff, eq_rec_constant] at hDir ⊢
        simp only [hi1, ↓reduceDIte, eq_rec_constant] at state
        exact P₂.receiveChallenge ⟨⟨i - m, sorry⟩, hDir⟩ (dcast (sorry) state)

  /- The combined prover's output function has two cases:
  - if the second protocol is empty, then it is the composition of the first prover's output
    function, the second prover's input function, and the second prover's output function.
  - if the second protocol is non-empty, then it is the second prover's output function. -/
  output := fun state => by
    dsimp [Fin.append, Fin.addCases, Fin.tail, Fin.cast, Fin.last, Fin.subNat] at state
    by_cases hn : n = 0
    · simp only [hn, add_zero, lt_add_iff_pos_right, Order.lt_one_iff,
        ↓reduceDIte] at state
      exact (do
        let ctxIn₂ ← P₁.output state
        letI state₂ := P₂.input ctxIn₂
        P₂.output (dcast (sorry) state₂))
    · haveI : m + n - (m + 1) + 1 = n := sorry
      simp only [Order.lt_add_one_iff, add_le_iff_nonpos_right,
        nonpos_iff_eq_zero, hn, ↓reduceDIte, eq_rec_constant] at state
      exact P₂.output (dcast (sorry) state)

namespace Prover

variable {P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}

include n in
/-- Sequential composition preserves pure prover output, including empty components. -/
theorem OutputIsPure.append (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : P₁.OutputIsPure) (h₂ : P₂.OutputIsPure) :
    (P₁.append P₂).OutputIsPure := sorry

include P₁ in
/-- Sequential composition of provers with pure output has pure output. -/
instance instOutputIsPureAppend [h₁ : P₁.OutputIsPure] [h₂ : P₂.OutputIsPure] :
    (P₁.append P₂).OutputIsPure := sorry

end Prover

/-- Run the first verifier on the transcript prefix, then pass its output statement to the
second verifier on the transcript suffix. Failure in either verifier propagates. -/
def Verifier.append (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂) :
      Verifier oSpec Stmt₁ Stmt₃ (pSpec₁ ++ₚ pSpec₂) where
  verify := fun stmt transcript => do
    return ← V₂.verify (← V₁.verify stmt transcript.fst) transcript.snd

/-- Compose the component provers and verifiers of two reductions. -/
def Reduction.append (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂) :
      Reduction oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂) where
  prover := Prover.append R₁.prover R₂.prover
  verifier := Verifier.append R₁.verifier R₂.verifier

section ChallengeSampling

variable [inst₁ : ∀ i, SampleableType (pSpec₁.Challenge i)]
    [inst₂ : ∀ i, SampleableType (pSpec₂.Challenge i)]

end ChallengeSampling

section OracleProtocol

variable [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
  [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
  {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
  {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]

include m n in
theorem message_interface_inl (i : pSpec₁.MessageIdx) : HEq (Oₘ₁ i)
    (inferInstance : OracleInterface ((pSpec₁ ++ₚ pSpec₂).Message (MessageIdx.inl i))) := sorry

include m n in
theorem message_interface_inr (i : pSpec₂.MessageIdx) : HEq (Oₘ₂ i)
    (inferInstance : OracleInterface ((pSpec₁ ++ₚ pSpec₂).Message (MessageIdx.inr i))) := sorry

abbrev AppendSpec :=
  oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ)

def messageQueryInl : QueryImpl [pSpec₁.Message]ₒ (OracleComp
    (AppendSpec (oSpec := oSpec) (OStmt₁ := OStmt₁) (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂))) :=
  fun q => by
    rcases q with ⟨i, q⟩
    have hType : pSpec₁.Message i = (pSpec₁ ++ₚ pSpec₂).Message (MessageIdx.inl i) := by
      simp [MessageIdx.inl, ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_left]
    exact OracleVerifier.queryAlongHEq (Oₘ₁ i) inferInstance hType (message_interface_inl i)
      (fun t => ((QueryImpl.id' [(pSpec₁ ++ₚ pSpec₂).Message]ₒ).liftTarget
        (OracleComp (AppendSpec (oSpec := oSpec) (OStmt₁ := OStmt₁))))
          ⟨MessageIdx.inl i, t⟩) q

def messageQueryInr : QueryImpl [pSpec₂.Message]ₒ (OracleComp
    (AppendSpec (oSpec := oSpec) (OStmt₁ := OStmt₁) (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂))) :=
  fun q => by
    rcases q with ⟨i, q⟩
    have hType : pSpec₂.Message i = (pSpec₁ ++ₚ pSpec₂).Message (MessageIdx.inr i) := by
      simp [MessageIdx.inr, ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_right]
    exact OracleVerifier.queryAlongHEq (Oₘ₂ i) inferInstance hType (message_interface_inr i)
      (fun t => ((QueryImpl.id' [(pSpec₁ ++ₚ pSpec₂).Message]ₒ).liftTarget
        (OracleComp (AppendSpec (oSpec := oSpec) (OStmt₁ := OStmt₁))))
          ⟨MessageIdx.inr i, t⟩) q

def firstQueryImpl : QueryImpl (oSpec + ([OStmt₁]ₒ + [pSpec₁.Message]ₒ))
    (OracleComp (AppendSpec (oSpec := oSpec) (OStmt₁ := OStmt₁)
      (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂))) :=
  ((QueryImpl.id' oSpec).liftTarget (OracleComp
    (AppendSpec (oSpec := oSpec) (OStmt₁ := OStmt₁)
      (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)))) +
    (((QueryImpl.id' [OStmt₁]ₒ).liftTarget (OracleComp
      (AppendSpec (oSpec := oSpec) (OStmt₁ := OStmt₁)
        (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)))) +
      messageQueryInl (oSpec := oSpec) (OStmt₁ := OStmt₁)
        (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂))

def secondQueryImpl
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (challenges : pSpec₁.Challenges) :
    QueryImpl (oSpec + ([OStmt₂]ₒ + [pSpec₂.Message]ₒ))
      (OracleComp (AppendSpec (oSpec := oSpec) (OStmt₁ := OStmt₁)
        (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂))) :=
  ((QueryImpl.id' oSpec).liftTarget (OracleComp
    (AppendSpec (oSpec := oSpec) (OStmt₁ := OStmt₁)
      (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)))) +
    ((fun q => simulateQ
      (firstQueryImpl (oSpec := oSpec) (OStmt₁ := OStmt₁)
        (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂))
      (V₁.simulateOutputQuery challenges q)) +
      messageQueryInr (oSpec := oSpec) (OStmt₁ := OStmt₁)
        (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂))

def appendOutputSimulation
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂) :
    OracleOutputSimulation oSpec OStmt₁ OStmt₃ (pSpec₁ ++ₚ pSpec₂) where
  materializeOutput := fun challenges oStmt messages =>
    V₂.materializeOutput challenges.snd
      (V₁.materializeOutput challenges.fst oStmt messages.fst) messages.snd
  simulateOutputQuery := fun challenges q =>
    simulateQ (secondQueryImpl V₁ challenges.fst)
      (V₂.simulateOutputQuery challenges.snd q)
  simulateOutputQuery_eq := sorry

def OracleVerifier.append (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂) :
      OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₃ OStmt₃ (pSpec₁ ++ₚ pSpec₂) where
  verify := fun stmt challenges => do
    let stmt₂ ← simulateQ
      (firstQueryImpl (oSpec := oSpec) (OStmt₁ := OStmt₁))
      (V₁.verify stmt challenges.fst)
    simulateQ (secondQueryImpl V₁ challenges.fst)
      (V₂.verify stmt₂ challenges.snd)

  outputOracle := .inr (appendOutputSimulation V₁ V₂)

/-- Sequential composition of oracle reductions is just the sequential composition of the oracle
  provers and oracle verifiers. -/
def OracleReduction.append (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂) :
      OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₃ OStmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂) where
  prover := Prover.append R₁.prover R₂.prover
  verifier := OracleVerifier.append R₁.verifier R₂.verifier

end OracleProtocol
