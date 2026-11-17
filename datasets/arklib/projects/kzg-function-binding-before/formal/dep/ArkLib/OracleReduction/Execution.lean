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
public import dep.VCVio.OracleComp.Support
public import dep.dep.CslibCompat.Basic
public import dep.dep.CslibCompat.Free

@[expose] public section

open OracleComp OracleSpec SubSpec ProtocolSpec

universe u v

section Execution

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
 {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
  [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)] {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}

namespace Prover

/--
Prover's function for processing the next round, given the current result of the previous round, and
a function for getting the challenge.
-/
@[inline, specialize]
def processRound (j : Fin n)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × prover.PrvState j.castSucc)) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ)
        (pSpec.Transcript j.succ × prover.PrvState j.succ) := do
  let ⟨transcript, state⟩ ← currentResult
  match hDir : pSpec.dir j with
  | .V_to_P => do
    let challenge ← pSpec.getChallenge ⟨j, hDir⟩
    letI newState := (← prover.receiveChallenge ⟨j, hDir⟩ state) challenge
    return ⟨transcript.concat challenge, newState⟩
  | .P_to_V => do
    let ⟨msg, newState⟩ ← prover.sendMessage ⟨j, hDir⟩ state
    return ⟨transcript.concat msg, newState⟩

/-- Run the prover in an interactive reduction up to round index `i`, via first inputting the
  statement and witness, and then processing each round up to round `i`. Returns the transcript up
  to round `i`, and the prover's state after round `i`.
-/
@[inline, specialize]
def runToRound (i : Fin (n + 1))
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ) (pSpec.Transcript i × prover.PrvState i) :=
  Fin.induction
    (pure ⟨default, prover.input (stmt, wit)⟩)
    (prover.processRound)
    i

/-- Run the prover in an interactive reduction. Returns the output statement and witness, and the
  transcript. See `runWithLog` for a version that additionally returns the log of the
  prover's oracle queries.
-/
@[inline, specialize]
def run (stmt : StmtIn) (wit : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ) (FullTranscript pSpec × StmtOut × WitOut) := do
  let ⟨transcript, state⟩ ← prover.runToRound (Fin.last n) stmt wit
  return ⟨transcript, ← prover.output state⟩

end Prover

/-- Run the (non-oracle) verifier in an interactive reduction. It takes in the input statement and
  the transcript, and return the output statement.
-/
@[inline, specialize, reducible]
def Verifier.run (stmt : StmtIn) (transcript : FullTranscript pSpec)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) : OptionT (OracleComp oSpec) StmtOut :=
  verifier.verify stmt transcript

/-- Run the oracle verifier in the interactive protocol. Returns the verifier's output, including
    both the output statement and oracle statements, and the log of queries made by the verifier.
-/
@[inline, specialize]
def OracleVerifier.run [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    (stmt : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (transcript : FullTranscript pSpec)
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :
      OptionT (OracleComp oSpec) (StmtOut × (∀ i, OStmtOut i)) :=
  verifier.toVerifier.run ⟨stmt, oStmtIn⟩ transcript

/-- An execution of an interactive reduction on a given initial statement and witness. Consists of
  first running the prover, and then the verifier. Returns the full transcript, the output statement
  and witness from the prover, and the output statement from the verifier.

  See `Reduction.runWithLog` for a version that additionally returns the logs of the prover's and
  the verifier's oracle queries.
-/
@[inline, specialize]
def Reduction.run (stmt : StmtIn) (wit : WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
        ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut) := do
  -- `ctxOut` contains both the output statement and witness after running the prover
  let proverResult ← reduction.prover.run stmt wit
  let stmtOut ← liftM (reduction.verifier.run stmt proverResult.1).run
  return ⟨proverResult, ← stmtOut.getM⟩

/-- Run a reduction and return only the verifier's output statement, discarding the full transcript
  and prover witness. Useful when only the final verdict matters (e.g. for `Proof`s). -/
def Reduction.verdict (stmt : StmtIn) (wit : WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) StmtOut := do
  let ⟨_, stmtOut⟩ ← reduction.run stmt wit
  return stmtOut

/-- Run a reduction on `L` instances (given by indexed statements and witnesses), and sequence the
  full successful run results. Returns `none` if any instance fails, otherwise returns a function
  from indices to the full run data. -/
def Reduction.allRuns {L : ℕ}
    (stmts : Fin L → StmtIn) (wits : Fin L → WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ)
        (Option (Fin L → ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut))) := do
  let results ← (Vector.ofFn id).mapM fun i => (reduction.run (stmts i) (wits i)).run
  return (results.mapM id).map fun v => fun i => v[i]

/-- Run a reduction on `L` instances and project each successful full run result through `extract`.
  Returns `none` if any instance fails, otherwise returns the indexed extracted outputs. -/
def Reduction.allOutputs {L : ℕ} {α : Type}
    (extract : ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut) → α)
    (stmts : Fin L → StmtIn) (wits : Fin L → WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ) (Option (Fin L → α)) := do
  let results ← reduction.allRuns stmts wits
  return results.map fun resultOf => fun i => extract (resultOf i)

/-- Run a reduction on `L` instances (given by indexed statements and witnesses), and sequence the
  results. Returns `none` if any instance fails, otherwise returns a function from indices to
  the verifier's output statements. -/
def Reduction.allVerdicts {L : ℕ}
    (stmts : Fin L → StmtIn) (wits : Fin L → WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ) (Option (Fin L → StmtOut)) := do
  let results ← (Vector.ofFn id).mapM fun i => (reduction.verdict (stmts i) (wits i)).run
  return (results.mapM id).map fun v => fun i => v[i]

/-- Run an interactive oracle reduction. Returns the full transcript, the output statement and
  witness, the log of all prover's oracle queries, and the log of all verifier's oracle queries to
  the prover's messages and to the shared oracle.
-/
@[inline, specialize]
def OracleReduction.run [∀ i, OracleInterface (pSpec.Message i)]
    (stmt : StmtIn) (oStmt : ∀ i, OStmtIn i) (wit : WitIn)
    (reduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
        ((FullTranscript pSpec × (StmtOut × ∀ i, OStmtOut i) × WitOut) ×
          (StmtOut × ∀ i, OStmtOut i)) := do
  let proverResult ← reduction.prover.run ⟨stmt, oStmt⟩ wit
  let stmtOut ← liftM (reduction.verifier.run stmt oStmt proverResult.1).run
  return ⟨proverResult, ← stmtOut.getM⟩

end Execution

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]

section Trivial

end Trivial

section SingleMessage

variable {pSpec : ProtocolSpec 1}

end SingleMessage

section Classes

variable {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type}
    {pSpec : ProtocolSpec 2}

end Classes
