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
public import dep.ArkLib.Data.Fin.Tuple.Defs
public import dep.ArkLib.Data.Fin.Tuple.Lemmas
public import dep.ArkLib.Data.Fin.Tuple.Notation
public import dep.ArkLib.OracleReduction.OracleInterface
public import dep.ArkLib.OracleReduction.Prelude
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
public import dep.ToMathlib.MeasureTheory.DiscreteInstances
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
public import dep.VCVio.EvalDist.Defs.Support.Failure
public import dep.VCVio.EvalDist.EvalDistEq
public import dep.VCVio.EvalDist.Instances.OptionT
public import dep.VCVio.EvalDist.Monad.Seq.Measure
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
public import dep.VCVio.OracleComp.SimSemantics.QueryImpl.Constructions.Core
public import dep.VCVio.OracleComp.SimSemantics.ReaderT.Basic
public import dep.VCVio.OracleComp.SimSemantics.SimulateQ
public import dep.VCVio.OracleComp.Support
public import dep.dep.CslibCompat.Basic
public import dep.dep.CslibCompat.Free

@[expose] public section

universe u v

open OracleComp OracleSpec

/-- A protocol specification for an interactive protocol with `n` steps consists of:
- A vector of directions `dir` for each step, which is either `.P_to_V` (the prover sends a message
  to the verifier) or `.V_to_P` (the verifier sends a challenge to the prover).
- A vector of types `«Type»` for each step, which is the type of the message or challenge sent in
  that step. -/
@[ext]
structure ProtocolSpec (n : ℕ) where
  /-- The direction of each message in the protocol. -/
  dir : Fin n → Direction
  /-- The type of each message in the protocol. -/
  «Type» : Fin n → Type
deriving Inhabited

variable {n : ℕ}

namespace ProtocolSpec

section Defs

/-- The empty protocol specification, with no messages or challenges, written as `!p[]`. -/
@[reducible]
def empty : ProtocolSpec 0 := ⟨!v[], !v[]⟩

@[inherit_doc] notation "!p[]" => empty

/-- Subtype of `Fin n` for the indices corresponding to messages in a protocol specification -/
@[reducible, simp]
def MessageIdx (pSpec : ProtocolSpec n) :=
  {i : Fin n // pSpec.dir i = Direction.P_to_V}

/-- Subtype of `Fin n` for the indices corresponding to challenges in a protocol specification -/
@[reducible, simp]
def ChallengeIdx (pSpec : ProtocolSpec n) :=
  {i : Fin n // pSpec.dir i = Direction.V_to_P}

instance {pSpec : ProtocolSpec n} : CoeHead (MessageIdx pSpec) (Fin n) where
  coe := fun i => i.1

instance {pSpec : ProtocolSpec n} : CoeHead (ChallengeIdx pSpec) (Fin n) where
  coe := fun i => i.1

/-- The type of the `i`-th message in a protocol specification.

This does not distinguish between messages received in full or as an oracle. -/
@[reducible, inline, specialize, simp]
def Message (pSpec : ProtocolSpec n) (i : MessageIdx pSpec) := pSpec.«Type» i.val

/-- The type of the `i`-th challenge in a protocol specification -/
@[reducible, inline, specialize, simp]
def Challenge (pSpec : ProtocolSpec n) (i : ChallengeIdx pSpec) := pSpec.«Type» i.val

/-- The type of all messages in a protocol specification. Uncurried version of `Message`. -/
@[reducible, inline, specialize]
def Messages (pSpec : ProtocolSpec n) : Type := ∀ i, pSpec.Message i

/-- The type of all challenges in a protocol specification -/
@[reducible, inline, specialize]
def Challenges (pSpec : ProtocolSpec n) : Type := ∀ i, pSpec.Challenge i

/-- The (full)) transcript of an interactive protocol, which is a list of messages and challenges.

Note that this is definitionally equal to `Transcript (Fin.last n) pSpec`. -/
@[reducible, inline, specialize]
def FullTranscript (pSpec : ProtocolSpec n) := (i : Fin n) → pSpec.«Type» i

section Restrict

variable {n : ℕ}

/-- Take the first `m ≤ n` rounds of a `ProtocolSpec n` -/
@[implicit_reducible]
def take (m : ℕ) (h : m ≤ n) (pSpec : ProtocolSpec n) : ProtocolSpec m :=
  {dir := Fin.take m h pSpec.dir, «Type» := Fin.take m h pSpec.«Type»}

/-- Drop the first `m ≤ n` rounds of a `ProtocolSpec n` -/
def drop (m : ℕ) (h : m ≤ n) (pSpec : ProtocolSpec n) : ProtocolSpec (n - m) :=
  {dir := Fin.drop m h pSpec.dir, «Type» := Fin.drop m h pSpec.«Type»}

/-- Extract the slice of the rounds of a `ProtocolSpec n` from `start` to `stop - 1`. -/
def extract (start stop : ℕ) (h1 : start ≤ stop) (h2 : stop ≤ n) (pSpec : ProtocolSpec n) :
    ProtocolSpec (stop - start) where
  dir := Fin.extract start stop h1 h2 pSpec.dir
  «Type» := Fin.extract start stop h1 h2 pSpec.«Type»

instance : SliceLT (ProtocolSpec n) ℕ
    (fun _ stop => stop ≤ n)
    (fun _ stop _ => ProtocolSpec stop)
    where
  sliceLT := fun v stop h => take stop h v

instance : SliceGE (ProtocolSpec n) ℕ
    (fun _ start => start ≤ n)
    (fun _ start _ => ProtocolSpec (n - start))
    where
  sliceGE := fun v start h => drop start h v

instance : Slice (ProtocolSpec n) ℕ ℕ
    (fun _ start stop => start ≤ stop ∧ stop ≤ n)
    (fun _ start stop _ => ProtocolSpec (stop - start))
    where
  slice := fun v start stop h => extract start stop h.1 h.2 v

variable {m start stop : ℕ} {h : m ≤ n} {h1 : start ≤ stop} {h2 : stop ≤ n}
  {pSpec : ProtocolSpec n}

namespace FullTranscript

variable {pSpec : ProtocolSpec n}

/-- Take the first `m ≤ n` rounds of a (full) transcript for a protocol specification `pSpec` -/
abbrev take (m : ℕ) (h : m ≤ n)
    (transcript : FullTranscript pSpec) : FullTranscript (pSpec.take m h) :=
  Fin.take m h transcript

abbrev drop (m : ℕ) (h : m ≤ n)
    (transcript : FullTranscript pSpec) : FullTranscript (pSpec.drop m h) :=
  Fin.drop m h transcript

abbrev extract (start stop : ℕ) (h1 : start ≤ stop) (h2 : stop ≤ n)
    (transcript : FullTranscript pSpec) : FullTranscript (pSpec.extract start stop h1 h2) :=
  Fin.extract start stop h1 h2 transcript

instance : SliceLT (FullTranscript pSpec) ℕ
    (fun _ stop => stop ≤ n)
    (fun _ stop _ => FullTranscript (pSpec⟦:stop⟧))
    where
  sliceLT := fun v stop h => take stop h v

instance : SliceGE (FullTranscript pSpec) ℕ
    (fun _ start => start ≤ n)
    (fun _ start _ => FullTranscript (pSpec⟦start:⟧))
    where
  sliceGE := fun v start h => drop start h v

instance : Slice (FullTranscript pSpec) ℕ ℕ
    (fun _ start stop => start ≤ stop ∧ stop ≤ n)
    (fun _ start stop _ => FullTranscript (pSpec⟦start:stop⟧))
    where
  slice := fun v start stop h => extract start stop h.1 h.2 v

variable {m start stop : ℕ} {h : m ≤ n} {h1 : start ≤ stop} {h2 : stop ≤ n}
  {pSpec : ProtocolSpec n} {transcript : FullTranscript pSpec}

end FullTranscript

end Restrict

/-- Subtype of `Fin k` for the indices corresponding to messages in a protocol specification up to
  round `k` -/
@[reducible, simp]
def MessageIdxUpTo (k : Fin (n + 1)) (pSpec : ProtocolSpec n) : Type :=
  (pSpec⟦:k.val⟧).MessageIdx

/-- Subtype of `Fin k` for the indices corresponding to challenges in a protocol specification up to
  round `k` -/
@[reducible, simp]
def ChallengeIdxUpTo (k : Fin (n + 1)) (pSpec : ProtocolSpec n) : Type :=
  (pSpec⟦:k.val⟧).ChallengeIdx

/-- The indexed family of messages from the prover up to round `k`. -/
@[reducible, inline, specialize]
def MessageUpTo (k : Fin (n + 1)) (pSpec : ProtocolSpec n) (i : pSpec.MessageIdxUpTo k) :=
  (pSpec⟦:k.val⟧).Message i

/-- The type of all messages from the prover up to round `k`. -/
@[reducible, inline, specialize]
def MessagesUpTo (k : Fin (n + 1)) (pSpec : ProtocolSpec n) : Type :=
  ∀ i, pSpec.MessageUpTo k i

/-- The type of all challenges from the verifier up to round `k`. -/
@[reducible, inline, specialize]
def ChallengesUpTo (k : Fin (n + 1)) (pSpec : ProtocolSpec n) : Type :=
  ∀ i, (pSpec.take k k.is_le).Challenge i

/-- A (partial) transcript of a protocol specification, indexed by some `k : Fin (n + 1)`, is a
list of messages from the protocol for all indices `i` less than `k`.

This is defined as the full transcript of the protocol specification up to round `k`. -/
@[reducible, inline, specialize]
def Transcript (k : Fin (n + 1)) (pSpec : ProtocolSpec n) : Type :=
  (pSpec⟦:k.val⟧).FullTranscript

end Defs

section Instances

/-- There is only one protocol specification with 0 messages (the empty one) -/
instance : Unique (ProtocolSpec 0) where
  default := empty
  uniq := fun ⟨_, _⟩ => sorry

instance : ∀ i, VCVCompatible (Challenge !p[] i) :=
  fun ⟨i, h⟩ =>
    (Fin.elim0 i : (h' : !p[].dir i = .V_to_P) → VCVCompatible (!p[].Challenge ⟨i, h'⟩)) h

instance : ∀ i, SampleableType (Challenge !p[] i) :=
  fun ⟨i, h⟩ =>
    (Fin.elim0 i : (h' : !p[].dir i = .V_to_P) → SampleableType (!p[].Challenge ⟨i, h'⟩)) h

instance : ∀ i, OracleInterface (Message !p[] i) :=
  fun ⟨i, h⟩ =>
    (Fin.elim0 i : (h' : !p[].dir i = .P_to_V) → OracleInterface (!p[].Message ⟨i, h'⟩)) h

instance : ∀ i, VCVCompatible ((default : ProtocolSpec 0).Challenge i) := fun ⟨i, _⟩ => Fin.elim0 i

instance : ∀ i, SampleableType ((default : ProtocolSpec 0).Challenge i) := fun ⟨i, _⟩ => Fin.elim0 i

instance : ∀ i, OracleInterface ((default : ProtocolSpec 0).Message i) := fun ⟨i, _⟩ => Fin.elim0 i

variable {Msg Chal : Type}

instance : IsEmpty (ChallengeIdx ⟨!v[.P_to_V], !v[Msg]⟩) := sorry

instance : Unique (MessageIdx ⟨!v[.P_to_V], !v[Msg]⟩) where
  default := ⟨0, sorry⟩
  uniq := fun i => sorry

instance [inst : OracleInterface Msg] : ∀ i, OracleInterface (Message ⟨!v[.P_to_V], !v[Msg]⟩ i)
  | ⟨0, _⟩ => inst

instance : ∀ i, VCVCompatible (Challenge ⟨!v[.P_to_V], !v[Msg]⟩ i)
  | ⟨0, h⟩ => nomatch h

instance : ∀ i, SampleableType (Challenge ⟨!v[.P_to_V], !v[Msg]⟩ i)
  | ⟨0, h⟩ => nomatch h

instance : IsEmpty (MessageIdx ⟨!v[.V_to_P], !v[Chal]⟩) := sorry

instance : Unique (ChallengeIdx ⟨!v[.V_to_P], !v[Chal]⟩) where
  default := ⟨0, sorry⟩
  uniq := fun i => sorry

instance : ∀ i, OracleInterface (Message ⟨!v[.V_to_P], !v[Chal]⟩ i)
  | ⟨0, h⟩ => nomatch h

instance [inst : VCVCompatible Chal] : ∀ i, VCVCompatible (Challenge ⟨!v[.V_to_P], !v[Chal]⟩ i)
  | ⟨0, _⟩ => inst

instance [inst : SampleableType Chal] : ∀ i, SampleableType (Challenge ⟨!v[.V_to_P], !v[Chal]⟩ i)
  | ⟨0, _⟩ => inst

variable {pSpec : ProtocolSpec n}

instance : Fintype (pSpec.MessageIdx) := Subtype.fintype (fun i => pSpec.dir i = .P_to_V)

instance : Fintype (pSpec.ChallengeIdx) := Subtype.fintype (fun i => pSpec.dir i = .V_to_P)

instance {k : Fin (n + 1)} : Fintype (pSpec.MessageIdxUpTo k) :=
  inferInstanceAs (Fintype <| MessageIdx (pSpec.take k k.is_le))

instance {k : Fin (n + 1)} : Fintype (pSpec.ChallengeIdxUpTo k) :=
  inferInstanceAs (Fintype <| ChallengeIdx (pSpec.take k k.is_le))

end Instances

variable {pSpec : ProtocolSpec n}

namespace MessagesUpTo

variable {k : Fin (n + 1)}

/-- For a tuple of messages up to round `k`, take the messages up to round `j : Fin (k + 1)` -/
def take (j : Fin (k + 1)) (messages : MessagesUpTo k pSpec) :
    MessagesUpTo (j.castLE (sorry)) pSpec :=
  fun i => messages ⟨i.val.castLE (sorry), i.property⟩

end MessagesUpTo

namespace Messages

/-- Take the messages up to round `j : Fin (n + 1)` -/
def take (j : Fin (n + 1)) (messages : Messages pSpec) : MessagesUpTo j pSpec :=
  by exact (by exact messages : MessagesUpTo (Fin.last n) pSpec).take j

end Messages

namespace ChallengesUpTo

variable {k : Fin (n + 1)}

/-- For a tuple of challenges up to round `k`, take the challenges up to round `j : Fin (k + 1)` -/
def take (j : Fin (k + 1)) (challenges : ChallengesUpTo k pSpec) :
    ChallengesUpTo (j.castLE (sorry)) pSpec :=
  fun i => challenges ⟨i.val.castLE (sorry), i.property⟩

end ChallengesUpTo

namespace Challenges

/-- Take the challenges up to round `j : Fin (n + 1)` -/
def take (j : Fin (n + 1)) (challenges : Challenges pSpec) : ChallengesUpTo j pSpec :=
  by exact (by exact challenges : ChallengesUpTo (Fin.last n) pSpec).take j

end Challenges

namespace MessagesUpTo

/-- There is only one transcript for the empty protocol,
  represented as `default : ProtocolSpec 0` -/
instance {k : Fin 1} : Unique (MessagesUpTo k (default : ProtocolSpec 0)) where
  default := fun i => ()
  uniq := sorry

/-- There is only one transcript for the empty protocol, represented as `![]` -/
instance {k : Fin 1} : Unique (MessagesUpTo k !p[]) where
  default := fun ⟨⟨i, h⟩, _⟩ => by
    have : k = 0 := Fin.fin_one_eq_zero k
    subst this; simp at h
  uniq := fun _ => sorry

/-- There is only one transcript for any protocol specification with cutoff index 0 -/
instance : Unique (MessagesUpTo 0 pSpec) where
  default := fun ⟨i, _⟩ => Fin.elim0 i
  uniq := fun T => sorry

def concat' {k : Fin n}
    (messages : (i : Fin k) → (pSpec.dir (i.castLE (sorry)) = .P_to_V
      → pSpec.«Type» (i.castLE (sorry))))
    (msg : (h : pSpec.dir k = .P_to_V) → pSpec.Message ⟨k, h⟩) :
    (i : Fin (k + 1)) → (pSpec.dir (i.castLE (sorry)) = .P_to_V) →
      pSpec.«Type» (i.castLE (sorry)) :=
  Fin.dconcat messages msg

/-- Concatenate the `k`-th message to the end of the tuple of messages up to round `k`, assuming
  round `k` is a message round. -/
def concat {k : Fin n} (messages : MessagesUpTo k.castSucc pSpec)
    (h : pSpec.dir k = .P_to_V) (msg : pSpec.Message ⟨k, h⟩) : MessagesUpTo k.succ pSpec :=
  fun ⟨i, h⟩ => (concat' (pSpec := pSpec) (fun i hi => messages ⟨i, hi⟩) (fun _ => msg)) i h

/-- Extend the tuple of messages up to round `k` to up to round `k + 1`, assuming round `k` is a
  challenge round (so no message from the prover is sent). -/
def extend {k : Fin n} (messages : MessagesUpTo k.castSucc pSpec)
    (h : pSpec.dir k = .V_to_P) : MessagesUpTo k.succ pSpec :=
  fun ⟨i, h⟩ => (concat' (pSpec := pSpec) (fun i hi => messages ⟨i, hi⟩) (fun h' => by aesop)) i h

instance [inst : ∀ i, DecidableEq (pSpec.Message i)] {k : Fin (n + 1)} :
    DecidableEq (MessagesUpTo k pSpec) :=
  @Fintype.decidablePiFintype _ _ (fun i => inst ⟨i.1.castLE (sorry), i.property⟩) _

end MessagesUpTo

namespace ChallengesUpTo

/-- There is only one transcript for the empty protocol,
  represented as `default : ProtocolSpec 0` -/
instance {k : Fin 1} : Unique (ChallengesUpTo k (default : ProtocolSpec 0)) where
  default := fun i => ()
  uniq := sorry

/-- There is only one transcript for the empty protocol, represented as `![]` -/
instance {k : Fin 1} : Unique (ChallengesUpTo k !p[]) where
  default := fun ⟨⟨i, h⟩, _⟩ => by
    have : k = 0 := Fin.fin_one_eq_zero k
    subst this; simp at h
  uniq := fun _ => sorry

/-- There is only one transcript for any protocol specification with cutoff index 0 -/
instance : Unique (ChallengesUpTo 0 pSpec) where
  default := fun ⟨i, _⟩ => Fin.elim0 i
  uniq := fun T => sorry

def concat' {k : Fin n}
    (challenges : (i : Fin k) → (pSpec.dir (i.castLE (sorry)) = .V_to_P
      → pSpec.«Type» (i.castLE (sorry))))
    (chal : (h : pSpec.dir k = .V_to_P) → pSpec.Challenge ⟨k, h⟩) :
    (i : Fin (k + 1)) → (pSpec.dir (i.castLE (sorry)) = .V_to_P) →
      pSpec.«Type» (i.castLE (sorry)) :=
  Fin.dconcat challenges chal

/-- Concatenate the `k`-th challenge to the end of the tuple of challenges up to round `k`, assuming
  round `k` is a challenge round. -/
def concat {k : Fin n} (challenges : ChallengesUpTo k.castSucc pSpec)
    (h : pSpec.dir k = .V_to_P) (chal : pSpec.Challenge ⟨k, h⟩) : ChallengesUpTo k.succ pSpec :=
  fun ⟨i, h⟩ => (concat' (pSpec := pSpec) (fun i hi => challenges ⟨i, hi⟩) (fun _ => chal)) i h

/-- Extend the tuple of challenges up to round `k` to up to round `k + 1`, assuming round `k` is a
  message round (so no challenge from the verifier is sent). -/
def extend {k : Fin n} (challenges : ChallengesUpTo k.castSucc pSpec)
    (h : pSpec.dir k = .P_to_V) : ChallengesUpTo k.succ pSpec :=
  fun ⟨i, h⟩ => (concat' (pSpec := pSpec) (fun i hi => challenges ⟨i, hi⟩) (fun h' => by aesop)) i h

end ChallengesUpTo

namespace Transcript

/-- There is only one transcript for the empty protocol -/
instance {k : Fin 1} : Unique (Transcript k (default : ProtocolSpec 0)) where
  default := fun i => ()
  uniq := sorry

/-- There is only one transcript for the empty protocol, represented as `![]` -/
instance {k : Fin 1} : Unique (Transcript k !p[]) where
  default := fun ⟨i, h⟩ => by
    have : k = 0 := Fin.fin_one_eq_zero k
    subst this; simp at h
  uniq := fun _ => sorry

/-- There is only one transcript for any protocol with cutoff index 0 -/
instance : Unique (Transcript 0 pSpec) where
  default := fun i => Fin.elim0 i
  uniq := fun T => sorry

/-- Concatenate a message to the end of a partial transcript. This is definitionally equivalent to
    `Fin.snoc`. -/
@[inline]
abbrev concat {m : Fin n} (msg : pSpec.«Type» m) (T : Transcript m.castSucc pSpec) :
    Transcript m.succ pSpec :=
  Fin.snoc T msg

variable {k : Fin (n + 1)}

end Transcript

namespace FullTranscript

@[reducible, inline, specialize]
def messages (transcript : FullTranscript pSpec) (i : MessageIdx pSpec) :=
  transcript i.val

@[reducible, inline, specialize]
def challenges (transcript : FullTranscript pSpec) (i : ChallengeIdx pSpec) :=
  transcript i.val

/-- There is only one full transcript (the empty one) for an empty protocol -/
instance : Unique (FullTranscript (default : ProtocolSpec 0)) := inferInstance

end FullTranscript

/-- The specification of whether each message in a protocol specification is available in full
    (`None`) or received as an oracle (`Some (instOracleInterface (pSpec.Message i))`).

    This is defined as a type class for notational convenience. -/
class OracleInterfaces (pSpec : ProtocolSpec n) where
  oracleInterfaces : ∀ i, Option (OracleInterface (pSpec.Message i))

section OracleInterfaces

variable (pSpec : ProtocolSpec n) [inst : OracleInterfaces pSpec]

/-- Subtype of `pSpec.MessageIdx` for messages that are received as oracles -/
@[reducible, inline, specialize]
def OracleMessageIdx := {i : pSpec.MessageIdx // (inst.oracleInterfaces i).isSome }

/-- The oracle interface instances for messages that are received as oracles -/
instance {i : OracleMessageIdx pSpec} : OracleInterface (pSpec.Message i) :=
  (inst.oracleInterfaces i).get i.2

end OracleInterfaces

/-- Turn each verifier's challenge into an oracle, where querying a unit type gives back the
    challenge.

  This is the default instance for the challenge oracle interface. It may be overridden by
  `challengeOracleInterface{SR/FS}` for state-restoration and/or Fiat-Shamir. -/
@[reducible, inline, specialize]
instance challengeOracleInterface {pSpec : ProtocolSpec n} :
    ∀ i, OracleInterface (pSpec.Challenge i) := fun i =>
  { Query := Unit
    toOC.spec := fun _ => pSpec.Challenge i
    toOC.impl := fun _ => do read }

/-- Query a verifier's challenge for a given challenge round `i`, given the default challenge
  oracle interface `challengeOracleInterface`.

  This is the default version for getting challenges, where we query the default
  `challengeOracleInterface`, which accepts trivial input. In contrast, `getChallenge{SR/FS}`
  requires an input statement and prior messages up to that round. -/
@[reducible, inline, specialize]
def getChallenge (pSpec : ProtocolSpec n) (i : pSpec.ChallengeIdx) :
    OracleComp ([pSpec.Challenge]ₒ'challengeOracleInterface) (pSpec.Challenge i) :=
  query (spec := [pSpec.Challenge]ₒ'challengeOracleInterface) ⟨i, ()⟩

/-- Define the query implementation for the verifier's challenge in terms of `ProbComp`.

This is a randomness oracle: it simply calls the `selectElem` method inherited from the
  `SampleableType` instance on the challenge types.
-/
def challengeQueryImpl {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)] :
    QueryImpl ([pSpec.Challenge]ₒ'challengeOracleInterface) ProbComp :=
  fun q => $ᵗ (pSpec.Challenge q.1)

section ChallengeReindex

variable {k l : ℕ} {p : ProtocolSpec k} {q : ProtocolSpec l}
  (f : p.ChallengeIdx → q.ChallengeIdx) (hf : ∀ i, q.Challenge (f i) = p.Challenge i)

/-- Forward map on challenge queries induced by an index map: reindex, keep the (trivial) query. -/
@[reducible] def challengeReindexQuery (t : [p.Challenge]ₒ.Domain) : [q.Challenge]ₒ.Domain :=
  ⟨f t.1, t.2⟩

/-- Backward map on challenge responses induced by an index map with matching challenge types:
transport the response along `hf`.

This is the intended transport, but note what does and does not force it. Neither `SubSpec` nor
`LawfulSubSpec` nor `DisjointSubSpec` pins it down: post-composing any fibrewise automorphism of
`p.Challenge t.1` yields a different `onResponse` with the *same* `onQuery` that is equally lawful
and equally disjoint. What pins this definition down is defeq evidence at the client sites — see
the `@[simp]` lemmas `liftM_challenge_append_inl` / `_inr` in `ProtocolSpec/SeqCompose.lean`, which
compute the lifted query and would break if the transport were changed. -/
@[reducible] def challengeReindexResponse (t : [p.Challenge]ₒ.Domain)
    (r : [q.Challenge]ₒ.Range (challengeReindexQuery f t)) : [p.Challenge]ₒ.Range t :=
  show p.Challenge t.1 from (hf t.1) ▸ (show q.Challenge (f t.1) from r)

/-- An embedding of challenge indices that preserves challenge types induces an inclusion of
challenge oracles.

`monadLift` is spelled out in lens form (rather than left to the class default) so that the lifted
query reduces during `simp` / `rw` matching; see the `OracleSpec.SubSpec` docstring. -/
@[reducible] def subSpecOfChallengeReindex : [p.Challenge]ₒ ⊂ₒ [q.Challenge]ₒ where
  monadLift qry := ⟨challengeReindexQuery f qry.input,
    qry.cont ∘ challengeReindexResponse f hf qry.input⟩
  onQuery := challengeReindexQuery f
  onResponse := challengeReindexResponse f hf

end ChallengeReindex

namespace MessagesUpTo

end MessagesUpTo

namespace Messages

end Messages

section TableReconstruction

variable {StmtIn : Type}

end TableReconstruction

end ProtocolSpec
