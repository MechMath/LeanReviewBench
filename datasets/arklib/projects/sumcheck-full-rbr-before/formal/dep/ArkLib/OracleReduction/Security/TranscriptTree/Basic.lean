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

open OracleComp OracleSpec ProtocolSpec

open scoped NNReal

namespace ProtocolSpec

variable {n : ℕ}

/-- A **tree of transcripts** for a protocol `pSpec`, branching only at challenge rounds.

The tree is indexed by the current round `m : Fin (n + 1)` (the rounds `m, m+1, …, n-1` are still to
come). Each challenge round `i` branches into `arity i` children. A `ChallengeTree pSpec arity 0`
(rooted at round `0`) describes a full tree of transcripts; reading the messages and challenges
along each root-to-leaf path recovers the corresponding `FullTranscript pSpec` (see
`ChallengeTree.transcripts`).

The challenge labels and subtrees of a challenge node are kept as two separate functions (rather
than a single function into a product) so that the recursive occurrence is not nested under `Prod`,
which the kernel forbids.

Note: The challenge arity is determined by the round index, not the path. So path-dependent
branching (e.g. "branch into 2 if the first challenge is `0`, branch into 3 if it's `1`") is not
currently supported. This may be generalized in the future, but keeps the current design simple
enough to follow the CWSS paper proofs.
-/
inductive ChallengeTree (pSpec : ProtocolSpec n) (arity : pSpec.ChallengeIdx → ℕ) :
    Fin (n + 1) → Type where
  /-- A leaf, reached once all `n` rounds have been processed. -/
  | leaf : ChallengeTree pSpec arity (Fin.last n)
  /-- A message round: the prover sends a single message `msg`, and the tree continues with a
    single child. -/
  | msgNode (m : Fin n) (h : pSpec.dir m = .P_to_V) (msg : pSpec.Message ⟨m, h⟩)
      (child : ChallengeTree pSpec arity m.succ) :
      ChallengeTree pSpec arity m.castSucc
  /-- A challenge round: the verifier branches into `arity ⟨m, h⟩` children, with `challenges j` the
    challenge value sent on branch `j` and `children j` the corresponding subtree. -/
  | chalNode (m : Fin n) (h : pSpec.dir m = .V_to_P)
      (challenges : Fin (arity ⟨m, h⟩) → pSpec.Challenge ⟨m, h⟩)
      (children : Fin (arity ⟨m, h⟩) → ChallengeTree pSpec arity m.succ) :
      ChallengeTree pSpec arity m.castSucc

/-- A protocol-generic structural predicate for challenge-tree nodes.

The `arity` field fixes the number of children at every challenge round, while `nodeOk` records
the combinatorial predicate that the sibling challenges at that round must satisfy. Plain special
soundness and coordinate-wise special soundness are both instances of this shape abstraction. -/
@[ext]
structure ChallengeTreeShape (pSpec : ProtocolSpec n) where
  /-- Branching factor at every verifier-to-prover round. -/
  arity : pSpec.ChallengeIdx → ℕ
  /-- Predicate on the sibling challenge labels at a verifier-to-prover round. -/
  nodeOk : (i : pSpec.ChallengeIdx) → (Fin (arity i) → pSpec.Challenge i) → Prop

namespace ChallengeTree

variable {pSpec : ProtocolSpec n} {arity : pSpec.ChallengeIdx → ℕ}

section Shape

variable (S : ChallengeTreeShape pSpec)

end Shape

section LeafPath

/-- A root-to-leaf path through a challenge tree. At challenge nodes, the path records the selected
child index; at message nodes there is only one child to follow. -/
inductive LeafPath : {m : Fin (n + 1)} → ChallengeTree pSpec arity m → Type where
  | leaf : LeafPath .leaf
  | msg {m : Fin n} {h : pSpec.dir m = .P_to_V} {msg : pSpec.Message ⟨m, h⟩}
      {child : ChallengeTree pSpec arity m.succ}
      (path : LeafPath child) : LeafPath (.msgNode m h msg child)
  | chal {m : Fin n} {h : pSpec.dir m = .V_to_P}
      {challenges : Fin (arity ⟨m, h⟩) → pSpec.Challenge ⟨m, h⟩}
      {children : Fin (arity ⟨m, h⟩) → ChallengeTree pSpec arity m.succ}
      (j : Fin (arity ⟨m, h⟩)) (path : LeafPath (children j)) :
      LeafPath (.chalNode m h challenges children)

namespace LeafPath

/-- **Every tree with positive branching has a leaf path**: descend through message nodes, and at
each challenge node take the first child.

This is what makes a subtree's transcript set inhabited, which matters as soon as verifiers are
allowed to *reject*: to rule out a rejecting prefix one must exhibit an actual transcript of the
subtree below it and contradict acceptance there. For pure verifiers the fact is never needed,
which is why it appears only now. Positivity is free for every coordinate-wise structure, whose
arity is `ℓᵢ·(kᵢ−1)+1` (`CWSSStructure.arity_pos`). -/
def some (harity : ∀ i, 0 < arity i) :
    {m : Fin (n + 1)} → (T : ChallengeTree pSpec arity m) → LeafPath T
  | _, .leaf => .leaf
  | _, .msgNode _ _ _ child => .msg (some harity child)
  | _, .chalNode m h _ children =>
      .chal ⟨0, harity ⟨m, h⟩⟩ (some harity (children ⟨0, harity ⟨m, h⟩⟩))

/-- Read the full transcript selected by a leaf path, extending an already-accumulated prefix. -/
def transcript :
    {m : Fin (n + 1)} → {T : ChallengeTree pSpec arity m} →
      LeafPath T → Transcript m pSpec → FullTranscript pSpec
  | _, _, .leaf, pre => pre
  | _, _, @LeafPath.msg _ _ _ _ _ message _ path, pre => path.transcript (pre.concat message)
  | _, _, @LeafPath.chal _ _ _ _ _ chals _ j path, pre =>
      path.transcript (pre.concat (chals j))

/-- Read the full transcript selected by a leaf path in a tree rooted at round `0`. -/
def fullTranscript {T : ChallengeTree pSpec arity 0} (path : LeafPath T) :
    FullTranscript pSpec :=
  path.transcript default

end LeafPath

end LeafPath

/-- Collect all root-to-leaf transcripts of a tree, given the partial transcript `pre` accumulated
  on the path from the root to the current node.

  At a message (resp. challenge) node we extend the prefix by the stored message (resp. by each
  child's challenge label) and recurse. At a leaf the accumulated prefix is a `FullTranscript`. -/
def transcripts :
    {m : Fin (n + 1)} → ChallengeTree pSpec arity m → Transcript m pSpec →
      List (FullTranscript pSpec)
  | _, .leaf, pre => [pre]
  | _, .msgNode _ _ msg child, pre => child.transcripts (pre.concat msg)
  | _, .chalNode m h challenges children, pre =>
      (List.finRange (arity ⟨m, h⟩)).flatMap fun j =>
        (children j).transcripts (pre.concat (challenges j))

/-- The transcripts of a full tree (rooted at round `0`), starting from the empty prefix. -/
def fullTranscripts (tree : ChallengeTree pSpec arity 0) : List (FullTranscript pSpec) :=
  tree.transcripts default

namespace LeafPath

end LeafPath

section IsAccepting

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  {arity : pSpec.ChallengeIdx → ℕ}

/-- A tree of transcripts is **accepting** with respect to an input statement `stmtIn` and an output
  language `langOut` if the verifier accepts every root-to-leaf transcript, i.e. for each such
  transcript the verifier outputs a statement in `langOut` with probability `1`.

  This is the tree-level analogue of the verifier's "accept" condition, phrased exactly as in the
  round-by-round state-function machinery (cf. `Verifier.StateFunction.toFun_full`). -/
def IsAccepting (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (langOut : Set StmtOut)
    (tree : ChallengeTree pSpec arity 0) : Prop :=
  ∀ tr ∈ tree.fullTranscripts,
    Pr{let stmtOut ← (OptionT.mk do
      (simulateQ impl (verifier.run stmtIn tr)).run' (← init))}[stmtOut ∈ langOut] = 1

end IsAccepting

section EscapeEvent

/-- An **escape event**: a statement-indexed predicate on full challenge trees, the
  hypothesis-side home of cryptographic escapes (e.g. "the openings derived from this tree collide
  under the fixed commitment key — a Module-SIS solution"). A tree-special-soundness certificate
  concludes `esc stmt tree ∨ extraction succeeds`, so an escape is an event on the *observable
  data*, never an output the extractor can fabricate.

  An escape event is a **trusted specification**, on the same footing as a package's
  `relIn`/`relOut`: nothing in the framework checks it. Two conditions every instance must satisfy,
  reviewed by reading its definition:

  - **hardness-tied and unconditional**: every `(stmt, tree)` satisfying the event must yield a
    break of the ambient assumption, checked against protocol parameters fixed outside the
    statement — at *every* pair, including statements no honest execution produces (composed
    events evaluate factor events at adversarially controllable intermediate statements);
  - **tree-determined**: the event may only constrain values computed from `(stmt, tree)`. It must
    not mention the verifier, the sampling `(init, impl)`, the *input* relation `relIn`, an
    extractor, or acceptance, since those smuggle in tautologies (e.g.
    `fun s t => (s, Ext s t) ∉ relIn` makes any certificate at `Ext` vacuous). Constraining the
    tree's per-branch responses by the *output* relation is fine and desirable — see below.

  Beyond honesty, aim for a **tight** event: one that fires only where extraction genuinely fails.
  Tightness is not enforced; a wider event just yields a weaker certificate, and a statement-only
  event like "some collision of this commitment exists" is honest yet worthless because it fires
  almost everywhere. Pinning the tree's per-branch responses to `relOut` (as
  `CoordinateWise.SingleRound.escEvent` does) is the standard way to get tightness.

  The trivial event `fun _ _ => False` is the escape-free degeneration (lossless: see
  `Verifier.treeSpecialSoundWith.withEscape`). -/
def EscapeEvent (Stmt : Type) (pSpec : ProtocolSpec n)
    (arity : pSpec.ChallengeIdx → ℕ) : Type :=
  Stmt → ChallengeTree pSpec arity 0 → Prop

end EscapeEvent

end ChallengeTree

end ProtocolSpec

namespace Verifier

open ProtocolSpec ProtocolSpec.ChallengeTree

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {σ : Type} {arity : pSpec.ChallengeIdx → ℕ}

end Verifier

namespace ProtocolSpec.ChallengeTree

open Verifier

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {σ : Type} {arity : pSpec.ChallengeIdx → ℕ}

/-- A **leaf witnessing**: one candidate output witness per root-to-leaf transcript of `tree`, or
  `none` where the witnessing declines.

  This is the "output witnesses" input of a reduction-of-knowledge extractor
  (`Extractor.TreeBased`). In a composed chain it is produced by the *downstream* extractor, which
  is exactly how a chain closes on a terminal link whose witness the tree itself contains. -/
def LeafWitnesses (tree : ChallengeTree pSpec arity 0) (WitOut : Type) : Type :=
  ChallengeTree.LeafPath tree → Option WitOut

namespace LeafWitnesses

end LeafWitnesses

section CanonWitnesses

end CanonWitnesses

end ProtocolSpec.ChallengeTree

namespace Extractor

open ProtocolSpec

/-- A **tree-based extractor**: assemble an input witness from the input statement, a tree of
  transcripts (rooted at round `0`), and one candidate output witness per leaf
  (`ChallengeTree.LeafWitnesses`) — or decline, returning `none`.

  The leaf witnessing is the second input of a reduction-of-knowledge extractor, and it is not
  eliminable: a `ChallengeTree` carries messages and challenges only, never an output witness, so
  for a cryptographic input relation no *total* function of `(stmtIn, tree)` alone can land in it.
  In a composed chain the witnessing is supplied by the downstream extractor, and the chain closes
  on a terminal link whose witness the tree does contain.

  `StmtOut` is deliberately **absent**: the extractor extracts a witness, full stop. Attributing
  output statements to leaves is the verifier's business, and output statements enter only through
  the soundness notion's validity premise (`ChallengeTree.LeafWitnesses.IsValid`). Both tree-based
  notions — plain `k`-special soundness and coordinate-wise special soundness — share this type, so
  it lives here on the shared `ChallengeTree`. -/
def TreeBased (StmtIn WitIn WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (arity : pSpec.ChallengeIdx → ℕ) : Type :=
  StmtIn → (tree : ProtocolSpec.ChallengeTree pSpec arity 0) →
    tree.LeafWitnesses WitOut → Option WitIn

end Extractor

namespace Verifier

open ProtocolSpec ProtocolSpec.ChallengeTree

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

end Verifier
