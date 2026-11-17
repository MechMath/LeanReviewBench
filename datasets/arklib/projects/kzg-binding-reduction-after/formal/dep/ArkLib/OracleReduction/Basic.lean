module

public import Batteries.Control.AlternativeMonad
public import Batteries.Control.OptionT
public import Batteries.Data.Fin.Fold
public import Batteries.Data.Vector.Lemmas
public import Batteries.Tactic.Lint
public import Batteries.Tactic.Lint.Basic
public import Cslib.Foundations.Control.Monad.IsMonadHom
public import Cslib.Foundations.Control.Monad.IsMonadHom.List
public import Cslib.Foundations.Data.PFunctor.Free
public import Cslib.Init
public import Init.Data.UInt.Lemmas
public import Lean.PrettyPrinter.Delaborator.Basic
public import Lean.PrettyPrinter.Formatter
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Finsupp.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
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
public import dep.ArkLib.OracleReduction.OracleInterface
public import dep.ArkLib.OracleReduction.Prelude
public import dep.ArkLib.OracleReduction.ProtocolSpec.Basic
public import dep.ArkLib.OracleReduction.ProtocolSpec.Cast
public import dep.ArkLib.OracleReduction.ProtocolSpec.SeqCompose
public import dep.CompPoly.Data.Classes.DCast
public import dep.CompPoly.Data.MvPolynomial.Notation
public import dep.CompPoly.ToMathlib.Finsupp.Fin
public import dep.CompPoly.ToMathlib.MvPolynomial.Equiv
public import dep.PolyFun.Control.Monad.Hom
public import dep.PolyFun.Control.Monad.Support
public import dep.PolyFun.Control.Monad.Support.Instances
public import dep.PolyFun.PFunctor.Basic
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
public import dep.ToCslib.Data.PFunctor.Free.Basic
public import dep.ToMathlib.Control.OptionT
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
public import dep.VCVio.OracleComp.SimSemantics.Append.Core
public import dep.VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import dep.VCVio.OracleComp.SimSemantics.ReaderT.Basic
public import dep.VCVio.OracleComp.SimSemantics.SimulateQ
public import dep.VCVio.OracleComp.Support
public import dep.dep.CslibCompat.Basic
public import dep.dep.CslibCompat.Free

@[expose] public section

open OracleComp OracleSpec SubSpec ProtocolSpec

/-- The type signature for the prover's state at each round.

For a protocol with `n` messages exchanged, there will be `(n + 1)` prover states, with the first
state before the first message and the last state after the last message. -/
@[ext]
structure ProverState (n : ℕ) where
  PrvState : Fin (n + 1) → Type

/-- Initialization of prover's state via inputting the statement and witness. -/
@[ext]
structure ProverInput (StmtIn WitIn PrvState : Type) where
  input : StmtIn × WitIn → PrvState

/-- Represents the interaction of a prover for a given protocol specification.

In each step, the prover gets access to the current state, then depending on the direction of the
step, the prover either sends a message or receives a challenge, and updates its state accordingly.

For maximum simplicity, we only define the `sendMessage` function as an oracle computation. All
other functions are pure. We may revisit this decision in the future.
-/
@[ext]
structure ProverRound {ι : Type} (oSpec : OracleSpec ι) {n : ℕ} (pSpec : ProtocolSpec n)
    extends ProverState n where
  /-- Send a message and update the prover's state -/
  sendMessage (i : MessageIdx pSpec) :
    PrvState i.1.castSucc → OracleComp oSpec (pSpec.Message i × PrvState i.1.succ)
  /-- Receive a challenge and update the prover's state -/
  receiveChallenge (i : ChallengeIdx pSpec) :
    PrvState i.1.castSucc → OracleComp oSpec (pSpec.Challenge i → PrvState i.1.succ)

/-- The output function of the prover, which takes in the prover's final state and returns an oracle
    computation that outputs some specified output type `Output`

  We note that an honest prover may output both the output statement and witness (for easier
  composability), but an adversarial prover in the knowledge soundness game may only output the
  witness.
-/
@[ext]
structure ProverOutput {ι : Type} (oSpec : OracleSpec ι) (Output PrvState : Type) where
  output : PrvState → OracleComp oSpec Output

/-- The type of honest provers for an interactive reduction with `n` messages. This consists of:

  - `PrvState 0`, ..., `PrvState n` are the types for the prover's state at each round
  - `input` initializes the prover's state by taking in the input statement and witness
  - `sendMessage` takes in the prover's state, then returns an oracle computation that outputs a
    message and the next prover's state
  - `receiveChallenge` takes in the prover's state, then returns an oracle computation that outputs
    a function that takes in a challenge and returns the next prover's state
  - `output` returns the output statement and witness from the prover's state

Note that the output statement by the prover is present only to facilitate composing honest provers
together. For completeness, we will require that the prover's output statement is always equal to
the verifier's output statement. For soundness and knowledge soundness, we will use more restricted
types of provers (see `ProverInteraction` and `ProverInteractionWithOutput`). -/
@[ext]
structure Prover {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type)
    {n : ℕ} (pSpec : ProtocolSpec n) extends
      ProverState n,
      ProverInput StmtIn WitIn (PrvState 0),
      ProverRound oSpec pSpec,
      ProverOutput oSpec (StmtOut × WitOut) (PrvState (Fin.last n))

/-- A verifier of an interactive protocol is a function that takes in the input statement and the
  transcript, and performs an oracle computation that outputs a new statement -/
@[ext]
structure Verifier {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn StmtOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) where
  verify : StmtIn → FullTranscript pSpec → OptionT (OracleComp oSpec) StmtOut

/-- An **(oracle) prover** in an interactive **oracle** reduction is a prover in the non-oracle
      reduction whose input statement also consists of the underlying messages for the oracle
      statements -/
@[reducible, inline]
def OracleProver {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) (WitIn : Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) (WitOut : Type)
    {n : ℕ} (pSpec : ProtocolSpec n) :=
  Prover oSpec (StmtIn × (∀ i, OStmtIn i)) WitIn (StmtOut × (∀ i, OStmtOut i)) WitOut pSpec

/-- A virtual output-oracle implementation for an `OracleVerifier`.

`materializeOutput` gives the extensional oracle value used by the existing bundled
`toVerifier` security interface. `simulateOutputQuery` gives the query-by-query VCV
implementation used by downstream oracle computations. `simulateOutputQuery_eq` requires
the two views to agree on every query. The output interface is a parameter of
both this structure and `OracleVerifier`; consequently the interface used to
produce virtual answers is definitionally the interface used by a downstream
verifier. -/
structure OracleOutputSimulation {ι : Type} (oSpec : OracleSpec ι)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type)
    {n : ℕ} (pSpec : ProtocolSpec n)
    [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)] where
  /-- Extensional materialization used by relation-facing bundled semantics. -/
  materializeOutput : pSpec.Challenges →
    (∀ i, OStmtIn i) → pSpec.Messages → (∀ i, OStmtOut i)
  /-- Query-by-query implementation of the virtual output family in terms of
  input statement oracles and prover-message oracles. -/
  simulateOutputQuery : pSpec.Challenges →
      QueryImpl [OStmtOut]ₒ
        (OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ)))
  /-- The VCV query implementation agrees with the extensional materialization. -/
  simulateOutputQuery_eq : ∀ challenges oStmt messages q,
      simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)
          (simulateOutputQuery challenges q) =
        pure ((Oₛₒ q.1).answer
          (materializeOutput challenges oStmt messages q.1) q.2)

/-- Legacy output-oracle semantics: every output is an input oracle or prover
message, with an explicit coherence proof for its public interface. -/
structure OracleOutputEmbedding {ιₛᵢ ιₛₒ : Type}
    (OStmtIn : ιₛᵢ → Type) {ιₘ : Type} (Message : ιₘ → Type)
    (OStmtOut : ιₛₒ → Type)
    [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    [Oₘ : ∀ i, OracleInterface (Message i)]
    [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)] where
  embed : ιₛₒ ↪ ιₛᵢ ⊕ ιₘ
  hEq : ∀ i, OStmtOut i = match embed i with
    | Sum.inl j => OStmtIn j
    | Sum.inr j => Message j
  outputInterface_heq : ∀ i, match embed i with
    | Sum.inl j => HEq (Oₛₒ i) (Oₛᵢ j)
    | Sum.inr j => HEq (Oₛₒ i) (Oₘ j)

/-- An **(oracle) verifier** of an interactive **oracle** reduction consists of:

  - an oracle computation `verify` that outputs the next statement. It may make queries to each of
    the prover's messages and each of the oracles present in the statement (according to a specified
    interface defined by `OracleInterface` instances).

  - output oracle statements `OStmtOut : ιₛₒ → Type`. A verifier may expose them as
    virtual oracles implemented query-by-query from its input and message oracles. Legacy
    verifiers instead select a subset of those source oracles through `embed` and `hEq`.

The virtual form supports derived output oracles without materializing them for downstream
oracle computations. Its agreement law connects that query-by-query implementation to the
extensional values used by the bundled security interface. -/
@[ext]
structure OracleVerifier {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type)
    {n : ℕ} (pSpec : ProtocolSpec n)
    [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
    where

  /-- The core verification logic. Takes the input statement `stmtIn` and all verifier challenges
  `challenges` (which are determined outside this function, typically by sampling for
  public-coin protocols). Returns the output statement `StmtOut` within an `OracleComp` that has
  access to external oracles `oSpec`, input statement oracles `OStmtIn`, and prover message
  oracles `pSpec.Message`. -/
  verify : StmtIn → pSpec.Challenges →
    OptionT (OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ))) StmtOut

  /-- The output family has exactly one semantic representation: either the
  legacy embedded-source form or a virtual query implementation. -/
  outputOracle :
    OracleOutputEmbedding OStmtIn pSpec.Message OStmtOut ⊕
      OracleOutputSimulation oSpec OStmtIn OStmtOut pSpec

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)

/-- Materialize an output-oracle representation independently of the verifier
that owns it. This is useful for adapters that construct and justify a new
output representation explicitly. -/
def materializeOutputOracle
    (outputOracle :
      OracleOutputEmbedding OStmtIn pSpec.Message OStmtOut ⊕
        OracleOutputSimulation oSpec OStmtIn OStmtOut pSpec)
    (challenges : pSpec.Challenges)
    (oStmt : ∀ i, OStmtIn i) (messages : pSpec.Messages) : ∀ i, OStmtOut i :=
  match outputOracle with
    | Sum.inr simulation => simulation.materializeOutput challenges oStmt messages
    | Sum.inl output => fun i => match h : output.embed i with
      | Sum.inl j => (output.hEq i ▸ h ▸ oStmt j : OStmtOut i)
      | Sum.inr j => (output.hEq i ▸ h ▸ messages j : OStmtOut i)

/-- Transport a query across explicit heterogeneous interface coherence. -/
def queryAlongHEq {A B : Type} (OA : OracleInterface A) (OB : OracleInterface B)
    (hType : A = B) (h : HEq OA OB) {ι' : Type} {spec : OracleSpec ι'}
    (impl : (q : OB.Query) → OracleComp spec (OB.Response q))
    (q : OA.Query) : OracleComp spec (OA.Response q) := by
  cases hType
  cases eq_of_heq h
  exact impl q

/-- Materialize the semantic output family, using a virtual simulation when
present and the legacy embedding otherwise. -/
def materializeOutput (challenges : pSpec.Challenges)
    (oStmt : ∀ i, OStmtIn i) (messages : pSpec.Messages) : ∀ i, OStmtOut i :=
  materializeOutputOracle verifier.outputOracle challenges oStmt messages

/-- Query any semantic output oracle in terms of the verifier's input and
message oracles. This operation hides the virtual/legacy distinction from
generic composition. -/
def simulateOutputQuery (challenges : pSpec.Challenges) :
    QueryImpl [OStmtOut]ₒ
      (OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ))) :=
  match verifier.outputOracle with
    | Sum.inr simulation => simulation.simulateOutputQuery challenges
    | Sum.inl output => fun q => match h : output.embed q.1 with
      | Sum.inl j => by
          have hType : OStmtOut q.1 = OStmtIn j := by
            simpa only [h] using output.hEq q.1
          have hi : HEq (Oₛₒ q.1) (Oₛᵢ j) := by
            simpa only [h] using output.outputInterface_heq q.1
          exact queryAlongHEq (Oₛₒ q.1) (Oₛᵢ j) hType hi
            (fun t : (Oₛᵢ j).Query =>
              ((QueryImpl.id' [OStmtIn]ₒ).liftTarget
                (OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ)))) ⟨j, t⟩) q.2
      | Sum.inr j => by
          have hType : OStmtOut q.1 = pSpec.Message j := by
            simpa only [h] using output.hEq q.1
          have hi : HEq (Oₛₒ q.1) (Oₘ j) := by
            simpa only [h] using output.outputInterface_heq q.1
          exact queryAlongHEq (Oₛₒ q.1) (Oₘ j) hType hi
            (fun t : (Oₘ j).Query =>
              ((QueryImpl.id' [pSpec.Message]ₒ).liftTarget
                (OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ)))) ⟨j, t⟩) q.2

/-- Querying the semantic output family agrees with materializing that family,
for both embedded and virtual output representations. -/
theorem simulateOutputQuery_eq
    (challenges : pSpec.Challenges) (oStmt : ∀ i, OStmtIn i)
    (messages : pSpec.Messages) (q : [OStmtOut]ₒ.Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)
        (verifier.simulateOutputQuery challenges q) =
      pure ((Oₛₒ q.1).answer
        (verifier.materializeOutput challenges oStmt messages q.1) q.2) := sorry

/-- An oracle verifier can be seen as a (non-oracle) verifier by providing the oracle interface
  using its knowledge of the oracle statements and the transcript messages in the clear -/
def toVerifier : Verifier oSpec (StmtIn × ∀ i, OStmtIn i) (StmtOut × (∀ i, OStmtOut i)) pSpec where
  verify := fun ⟨stmt, oStmt⟩ transcript => OptionT.mk <|
    Option.map (fun stmtOut =>
      (stmtOut, verifier.materializeOutput
        transcript.challenges oStmt transcript.messages)) <$>
      simulateQ (OracleInterface.simOracle2 oSpec oStmt transcript.messages)
        (verifier.verify stmt transcript.challenges).run

/-- A **non-adaptive** oracle verifier is an oracle verifier that makes a **fixed** list of queries
    to the input oracle statements and the prover's messages. These queries can depend on the input
    statement and the challenges, but later queries are not dependent on the responses of previous
    queries.

  Formally, we model this as a tuple of functions:
  - `queryOStmt`, which outputs a list of queries to the input oracle statements,
  - `queryMsg`, which outputs a list of queries to the prover's messages,
  - `verify`, which outputs the new statement from the query-response pairs.

  We allow querying the shared oracle (i.e. probabilistic sampling or random oracles) when deriving
  the output statement, but not on the list of queries made to the oracle statements or the prover's
  messages.

  Finally, we also allow for choosing a subset of the input oracle statements + the prover's
  messages to retain for the output oracle statements.
-/
structure NonAdaptive {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type)
    {n : ℕ} (pSpec : ProtocolSpec n)
    [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
    where

  /-- Makes a list of queries to each of the oracle statements, given the input statement and the
    challenges -/
  queryOStmt : StmtIn → (∀ i, pSpec.Challenge i) → List ((i : ιₛᵢ) × (Oₛᵢ i).Query)

  /-- Makes a list of queries to each of the prover's messages, given the input statement and the
    challenges -/
  queryMsg : StmtIn → (∀ i, pSpec.Challenge i) → List ((i : pSpec.MessageIdx) × (Oₘ i).Query)

  /-- From the query-response pairs, returns a computation that outputs the new output statement -/
  verify : StmtIn → (∀ i, pSpec.Challenge i) →
    List ((i : ιₛᵢ) × ((q : (Oₛᵢ i).Query) × (Oₛᵢ i).Response q)) →
    List ((i : pSpec.MessageIdx) × ((q : (Oₘ i).Query) × (Oₘ i).Response q)) →
      OracleComp oSpec StmtOut

  embed : ιₛₒ ↪ ιₛᵢ ⊕ pSpec.MessageIdx

  hEq : ∀ i, OStmtOut i = match embed i with
    | Sum.inl j => OStmtIn j
    | Sum.inr j => pSpec.Message j

  outputInterface_heq : ∀ i, match embed i with
    | Sum.inl j => HEq (Oₛₒ i) (Oₛᵢ j)
    | Sum.inr j => HEq (Oₛₒ i) (Oₘ j)

namespace NonAdaptive

end NonAdaptive

end OracleVerifier

/-- An **interactive reduction** for a given protocol specification `pSpec`, and relative to oracles
  defined by `oSpec`, consists of a prover and a verifier. -/
@[ext]
structure Reduction {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) where
  prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec
  verifier : Verifier oSpec StmtIn StmtOut pSpec

/-- An **interactive oracle reduction** for a given protocol specification `pSpec`, and relative to
  oracles defined by `oSpec`, consists of a prover and an **oracle** verifier. -/
@[ext]
structure OracleReduction {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) (WitIn : Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) (WitOut : Type)
    {n : ℕ} (pSpec : ProtocolSpec n)
    [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)] [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
    where
  prover : OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec
  verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec

/-- An **interactive proof (IP)** is an interactive reduction where the output statement is a
    boolean, the output witness is trivial (a `Unit`), and the relation checks whether the output
    statement is true. -/
@[reducible] def Proof {ι : Type} (oSpec : OracleSpec ι)
    (Statement Witness : Type) {n : ℕ} (pSpec : ProtocolSpec n) :=
  Reduction oSpec Statement Witness Bool Unit pSpec

/-- An **interactive oracle proof (IOP)** is an interactive oracle reduction where the output
    statement is a boolean, while both the output oracle statement & the output witness are
    trivial (`Unit` type).

    As a consequence, the output relation in an IOP is effectively a function `Bool → Prop`, which
    we can again assume to be the trivial one (sending `true` to `True`). -/
@[reducible] def OracleProof {ι : Type} (oSpec : OracleSpec ι)
    (Statement : Type) {ιₛᵢ : Type} (OStatement : ιₛᵢ → Type) (Witness : Type)
    {n : ℕ} (pSpec : ProtocolSpec n)
    [Oₛᵢ : ∀ i, OracleInterface (OStatement i)]
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)] :=
  @OracleReduction ι oSpec Statement ιₛᵢ OStatement Witness Bool Empty
    (fun _ : Empty => Unit) Unit n pSpec Oₛᵢ Oₘ (fun i => nomatch i)

/-- The verifier type underlying an interactive oracle proof. Its output-oracle
family is empty, so its interface is supplied by elimination rather than by a
global `OracleInterface Unit` instance. -/
@[reducible] def OracleProofVerifier {ι : Type} (oSpec : OracleSpec ι)
    (Statement : Type) {ιₛ : Type} (OStatement : ιₛ → Type)
    {n : ℕ} (pSpec : ProtocolSpec n)
    [Oₛ : ∀ i, OracleInterface (OStatement i)]
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)] :=
  @OracleVerifier ι oSpec Statement ιₛ OStatement Bool Empty
    (fun _ : Empty => Unit) n pSpec Oₛ Oₘ
      (fun i => nomatch i)

namespace OracleProofVerifier

end OracleProofVerifier

section Trivial

variable {ι : Type} {oSpec : OracleSpec ι}
    {Statement : Type} {ιₛ : Type} {OStatement : ιₛ → Type} {Witness : Type}
    [Oₛ : ∀ i, OracleInterface (OStatement i)]

/-- The trivial / identity prover, which does not send any messages to the verifier, and returns its
  input context (statement & witness) as output. -/
protected def Prover.id : Prover oSpec Statement Witness Statement Witness !p[] where
  PrvState := fun _ => Statement × Witness
  input := _root_.id
  sendMessage := fun i => Fin.elim0 i
  receiveChallenge := fun i => Fin.elim0 i
  output := pure

/-- The trivial / identity verifier, which does not receive any messages from the prover, and
  returns its input statement as output. -/
protected def Verifier.id : Verifier oSpec Statement Statement !p[] where
  verify := fun stmt _ => pure stmt

/-- The trivial / identity reduction, which consists of the trivial prover and verifier. -/
protected def Reduction.id : Reduction oSpec Statement Witness Statement Witness !p[] where
  prover := Prover.id
  verifier := Verifier.id

/-- The trivial / identity prover in an oracle reduction, which unfolds to the trivial prover for
  the associated non-oracle reduction. -/
protected def OracleProver.id :
    OracleProver oSpec Statement OStatement Witness Statement OStatement Witness !p[] :=
  Prover.id

/-- The trivial / identity verifier in an oracle reduction, which receives no messages from the
  prover, and returns its input statement as output. -/
protected def OracleVerifier.id :
    OracleVerifier oSpec Statement OStatement Statement OStatement !p[] where
  verify := fun stmt _ => pure stmt
  outputOracle := .inl {
    embed := Function.Embedding.inl
    hEq := fun _ => rfl
    outputInterface_heq := fun i => sorry }

/-- The trivial / identity oracle reduction, which consists of the trivial oracle prover and
  verifier. -/
protected def OracleReduction.id :
    OracleReduction oSpec Statement OStatement Witness Statement OStatement Witness !p[] :=
  ⟨OracleProver.id, OracleVerifier.id⟩

alias Prover.trivial := Prover.id

alias Verifier.trivial := Verifier.id

alias Reduction.trivial := Reduction.id

alias OracleProver.trivial := OracleProver.id

alias OracleVerifier.trivial := OracleVerifier.id

alias OracleReduction.trivial := OracleReduction.id

end Trivial

section Classes

namespace ProtocolSpec

variable {n : ℕ}

/-- A protocol specification with the prover speaking first -/
class ProverFirst (pSpec : ProtocolSpec n) [NeZero n] where
  prover_first' : pSpec.dir 0 = .P_to_V

class VerifierFirst (pSpec : ProtocolSpec n) [NeZero n] where
  verifier_first' : pSpec.dir 0 = .V_to_P

class ProverLast (pSpec : ProtocolSpec n) [inst : NeZero n] where
  prover_last' : pSpec.dir ⟨n - 1, by simp [Nat.pos_of_neZero]⟩ = .P_to_V

/-- A protocol specification with the verifier speaking last -/
class VerifierLast (pSpec : ProtocolSpec n) [NeZero n] where
  verifier_last' : pSpec.dir ⟨n - 1, by simp [Nat.pos_of_neZero]⟩ = .V_to_P

section SingleMessage

variable {pSpec : ProtocolSpec 1}

instance [ProverFirst pSpec] : ProverLast pSpec := sorry

instance [VerifierFirst pSpec] : VerifierLast pSpec := sorry

instance [h : ProverLast pSpec] : ProverFirst pSpec := sorry

instance [h : VerifierFirst pSpec] : VerifierFirst pSpec := sorry

instance [ProverFirst pSpec] : Unique (pSpec.MessageIdx) where
  default := ⟨0, sorry⟩
  uniq := fun ⟨i, _⟩ => sorry

instance [VerifierFirst pSpec] : Unique (pSpec.ChallengeIdx) where
  default := ⟨0, sorry⟩
  uniq := fun ⟨i, _⟩ => sorry

instance [h : ProverFirst pSpec] : IsEmpty (pSpec.ChallengeIdx) := sorry

instance [h : VerifierFirst pSpec] : IsEmpty (pSpec.MessageIdx) := sorry

instance [ProverFirst pSpec] : ∀ i, VCVCompatible (pSpec.Challenge i) := isEmptyElim

instance [VerifierFirst pSpec] : ∀ i, OracleInterface (pSpec.Message i) := isEmptyElim

instance [ProverFirst pSpec] [h : OracleInterface (pSpec.«Type» 0)] :
    ∀ i, OracleInterface (pSpec.Message i)
  | ⟨0, _⟩ => inferInstance

instance [VerifierFirst pSpec] [h : VCVCompatible (pSpec.«Type» 0)] :
    ∀ i, VCVCompatible (pSpec.Challenge i)
  | ⟨0, _⟩ => inferInstance

end SingleMessage

/-- A protocol specification with a single round of interaction consisting of two messages, with the
  prover speaking first and the verifier speaking last

This notation is currently somewhat ambiguous, given that there are other valid ways of defining a
"single-round" protocol, such as letting the verifier speaks first, letting the prover speaks
multiple times, etc. -/
class IsSingleRound (pSpec : ProtocolSpec 2) extends ProverFirst pSpec, VerifierLast pSpec

namespace IsSingleRound

variable {pSpec : ProtocolSpec 2}

/-- The first message is the only message from the prover to the verifier -/
instance [IsSingleRound pSpec] : Unique (pSpec.MessageIdx) where
  default := ⟨0, sorry⟩
  uniq := fun ⟨i, hi⟩ => sorry

/-- The second message is the only challenge from the verifier to the prover -/
instance [IsSingleRound pSpec] : Unique (pSpec.ChallengeIdx) where
  default := ⟨1, sorry⟩
  uniq := fun ⟨i, hi⟩ => sorry

instance [IsSingleRound pSpec] [h : OracleInterface (pSpec.Message default)] :
    (i : pSpec.MessageIdx) → OracleInterface (pSpec.Message i) := fun i => by
  haveI : i = default := Unique.uniq _ i
  subst this
  exact h

instance [IsSingleRound pSpec] [h : VCVCompatible (pSpec.Challenge default)] :
    (i : pSpec.ChallengeIdx) → VCVCompatible (pSpec.Challenge i) := fun i => by
  haveI : i = default := Unique.uniq _ i
  subst this
  exact h

end IsSingleRound

end ProtocolSpec

section IsPure

variable {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}

class Prover.IsPure (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) where
    is_pure : ∃ sendMessage : ∀ _, _ → _, ∀ i st,
      P.sendMessage i st = pure (sendMessage i st)

class Verifier.IsPure (V : Verifier oSpec StmtIn StmtOut pSpec) where
    is_pure : ∃ verify : _ → _ → _, ∀ stmtIn transcript,
      V.verify stmtIn transcript = pure (verify stmtIn transcript)

class Reduction.IsPure (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) where
    prover_is_pure : R.prover.IsPure
    verifier_is_pure : R.verifier.IsPure

end IsPure

end Classes
