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

universe u v

open OracleComp OracleSpec

namespace ProtocolSpec

variable {m n : ℕ}

/-- Adding a round with direction `dir` and type `Message` to the beginning of a `ProtocolSpec` -/
abbrev cons (pSpec : ProtocolSpec n) (dir : Direction) (Message : Type) :
    ProtocolSpec (n + 1) :=
  ⟨Fin.vcons dir pSpec.dir, Fin.vcons Message pSpec.Type⟩

/-- Concatenate a round with direction `dir` and type `Message` to the end of a `ProtocolSpec` -/
abbrev concat (pSpec : ProtocolSpec n) (dir : Direction) (Message : Type) :
    ProtocolSpec (n + 1) :=
  ⟨Fin.vconcat pSpec.dir dir, Fin.vconcat pSpec.Type Message⟩

/-- Appending two `ProtocolSpec`s -/
abbrev append (pSpec : ProtocolSpec m) (pSpec' : ProtocolSpec n) : ProtocolSpec (m + n) :=
  ⟨Fin.vappend pSpec.dir pSpec'.dir, Fin.vappend pSpec.Type pSpec'.Type⟩

@[inherit_doc]
infixl : 65 " ++ₚ " => ProtocolSpec.append

variable {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- Left type transport for `++ₚ` at a `castAdd` index: the appended spec's type
at an index in the first half is the left spec's type. -/
theorem append_Type_castAdd (i : Fin m) :
    (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.castAdd n i) = pSpec₁.«Type» i := sorry

/-- Right type transport for `++ₚ` at a `natAdd` index: the appended spec's type
at an index in the second half is the right spec's type. -/
theorem append_Type_natAdd (i : Fin n) :
    (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.natAdd m i) = pSpec₂.«Type» i := sorry

namespace Transcript

variable {k : Fin (m + n + 1)}

/-- The first half of a partial transcript for a concatenated protocol, up to round `k < m + n + 1`.

This is defined to be the full transcript for the first half if `k ≥ m`. -/
def fst (T : (pSpec₁ ++ₚ pSpec₂).Transcript k) : pSpec₁.Transcript ⟨min k m, sorry⟩ :=
  fun i => by
    have him : (i : ℕ) < min (k : ℕ) m := i.isLt
    exact _root_.cast
      (append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) ⟨i.val, sorry⟩)
      (T ⟨i.val, by omega⟩)

/-- The second half of a partial transcript for a concatenated protocol. -/
def snd (T : (pSpec₁ ++ₚ pSpec₂).Transcript k) : pSpec₂.Transcript ⟨k - m, sorry⟩ :=
  fun i => by
    have him : (i : ℕ) < (k : ℕ) - m := i.isLt
    have hk := k.isLt
    exact _root_.cast
      (append_Type_natAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) ⟨i.val, sorry⟩)
      (T ⟨m + i.val, by omega⟩)

end Transcript

namespace FullTranscript

/-- Appending two transcripts for two `ProtocolSpec`s -/
def append (T₁ : FullTranscript pSpec₁) (T₂ : FullTranscript pSpec₂) :
    FullTranscript (pSpec₁ ++ₚ pSpec₂) :=
  Fin.happend T₁ T₂

@[inherit_doc]
infixl : 65 " ++ₜ " => append

/-- Adding a message with a given direction and type to the end of a `Transcript` -/
def concat {pSpec : ProtocolSpec n} {NextMessage : Type}
    (T : FullTranscript pSpec) (dir : Direction) (msg : NextMessage) :
        FullTranscript (pSpec ++ₚ ⟨!v[dir], !v[NextMessage]⟩) :=
  Fin.hconcat T msg

/-- The first half of a transcript for a concatenated protocol -/
def fst (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) : FullTranscript pSpec₁ :=
  fun i => by
    simpa [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_left]
      using T (Fin.castAdd n i)

/-- The second half of a transcript for a concatenated protocol -/
def snd (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) : FullTranscript pSpec₂ :=
  fun i => by
    simpa [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_right]
      using T (Fin.natAdd m i)

end FullTranscript

def MessageIdx.inl (i : MessageIdx pSpec₁) : MessageIdx (pSpec₁ ++ₚ pSpec₂) :=
  ⟨Fin.castAdd n i.1, sorry⟩

def MessageIdx.inr (i : MessageIdx pSpec₂) : MessageIdx (pSpec₁ ++ₚ pSpec₂) :=
  ⟨Fin.natAdd m i.1, sorry⟩

def ChallengeIdx.inl (i : ChallengeIdx pSpec₁) : ChallengeIdx (pSpec₁ ++ₚ pSpec₂) :=
  ⟨Fin.castAdd n i.1, sorry⟩

def ChallengeIdx.inr (i : ChallengeIdx pSpec₂) : ChallengeIdx (pSpec₁ ++ₚ pSpec₂) :=
  ⟨Fin.natAdd m i.1, sorry⟩

/-- Restrict challenges for an appended protocol to its first component. -/
def Challenges.fst (challenges : (pSpec₁ ++ₚ pSpec₂).Challenges) : pSpec₁.Challenges :=
  fun i => by
    simpa [ChallengeIdx.inl, ProtocolSpec.append, Fin.vappend_eq_append,
      Fin.append_left] using challenges (ChallengeIdx.inl i)

/-- Restrict challenges for an appended protocol to its second component. -/
def Challenges.snd (challenges : (pSpec₁ ++ₚ pSpec₂).Challenges) : pSpec₂.Challenges :=
  fun i => by
    simpa [ChallengeIdx.inr, ProtocolSpec.append, Fin.vappend_eq_append,
      Fin.append_right] using challenges (ChallengeIdx.inr i)

/-- Restrict messages for an appended protocol to its first component. -/
def Messages.fst (messages : (pSpec₁ ++ₚ pSpec₂).Messages) : pSpec₁.Messages :=
  fun i => by
    simpa [MessageIdx.inl, ProtocolSpec.append, Fin.vappend_eq_append,
      Fin.append_left] using messages (MessageIdx.inl i)

/-- Restrict messages for an appended protocol to its second component. -/
def Messages.snd (messages : (pSpec₁ ++ₚ pSpec₂).Messages) : pSpec₂.Messages :=
  fun i => by
    simpa [MessageIdx.inr, ProtocolSpec.append, Fin.vappend_eq_append,
      Fin.append_right] using messages (MessageIdx.inr i)

/-- Sequential composition of a family of `ProtocolSpec`s, indexed by `i : Fin m`.

Defined for definitional equality, so that:
- `seqCompose !v[] = !p[]`
- `seqCompose !v[pSpec₁] = pSpec₁`
- `seqCompose !v[pSpec₁, pSpec₂] = pSpec₁ ++ₚ pSpec₂`
- `seqCompose !v[pSpec₁, pSpec₂, pSpec₃] = pSpec₁ ++ₚ (pSpec₂ ++ₚ pSpec₃)`
- and so on.

TODO: add notation `∑ i, pSpec i` for `seqCompose` -/
@[inline]
def seqCompose {m : ℕ} {n : Fin m → ℕ} (pSpec : ∀ i, ProtocolSpec (n i)) :
    ProtocolSpec (Fin.vsum n) where
  dir := Fin.vflatten (fun i => (pSpec i).dir)
  «Type» := Fin.vflatten (fun i => (pSpec i).Type)

namespace FullTranscript

end FullTranscript

section Append

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- If two protocols have sampleable challenges, then their concatenation also has sampleable
  challenges. -/
@[inline]
instance [h₁ : ∀ i, SampleableType (pSpec₁.Challenge i)]
    [h₂ : ∀ i, SampleableType (pSpec₂.Challenge i)] :
    ∀ i, SampleableType ((pSpec₁ ++ₚ pSpec₂).Challenge i) :=
  fun ⟨i, h⟩ => Fin.fappend₂ (A := Direction) (B := Type)
    (F := fun dir type => (h : dir = .V_to_P) → SampleableType type)
    (α₁ := pSpec₁.dir) (β₁ := pSpec₂.dir)
    (α₂ := pSpec₁.Type) (β₂ := pSpec₂.Type) (fun i h => h₁ ⟨i, h⟩) (fun i h => h₂ ⟨i, h⟩) i h

/-- If two protocols' challenge types are inhabited, then their concatenation's challenge types are
    also inhabited. -/
@[inline]
instance [h₁ : ∀ i, Inhabited (pSpec₁.Challenge i)]
    [h₂ : ∀ i, Inhabited (pSpec₂.Challenge i)] :
    ∀ i, Inhabited ((pSpec₁ ++ₚ pSpec₂).Challenge i) :=
  fun ⟨i, h⟩ => Fin.fappend₂ (A := Direction) (B := Type)
    (F := fun dir type => (h : dir = .V_to_P) → Inhabited type)
    (α₁ := pSpec₁.dir) (β₁ := pSpec₂.dir)
    (α₂ := pSpec₁.Type) (β₂ := pSpec₂.Type) (fun i h => h₁ ⟨i, h⟩) (fun i h => h₂ ⟨i, h⟩) i h

/-- If two protocols' challenge types are finite, then their concatenation's challenge types are
    also finite. -/
@[inline]
instance [h₁ : ∀ i, Fintype (pSpec₁.Challenge i)]
    [h₂ : ∀ i, Fintype (pSpec₂.Challenge i)] :
    ∀ i, Fintype ((pSpec₁ ++ₚ pSpec₂).Challenge i) :=
  fun ⟨i, h⟩ => Fin.fappend₂ (A := Direction) (B := Type)
    (F := fun dir type => (h : dir = .V_to_P) → Fintype type)
    (α₁ := pSpec₁.dir) (β₁ := pSpec₂.dir)
    (α₂ := pSpec₁.Type) (β₂ := pSpec₂.Type) (fun i h => h₁ ⟨i, h⟩) (fun i h => h₂ ⟨i, h⟩) i h

/-- If two protocols' messages have oracle representations, then their concatenation's messages also
    have oracle representations. -/
instance [O₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
    [O₂ : ∀ i, OracleInterface (pSpec₂.Message i)] :
    ∀ i, OracleInterface ((pSpec₁ ++ₚ pSpec₂).Message i) :=
  fun ⟨i, h⟩ => Fin.fappend₂ (A := Direction) (B := Type)
    (F := fun dir type => (h : dir = .P_to_V) → OracleInterface type)
    (α₁ := pSpec₁.dir) (β₁ := pSpec₂.dir)
    (α₂ := pSpec₁.Type) (β₂ := pSpec₂.Type) (fun i h => O₁ ⟨i, h⟩) (fun i h => O₂ ⟨i, h⟩) i h

instance : ∀ i, OracleInterface ((pSpec₁ ++ₚ pSpec₂).Challenge i) := challengeOracleInterface

/-- The challenge type of an appended protocol at a left-injected challenge index agrees with the
challenge type of the left component. This is the transport fact needed to move challenge data
across `++ₚ`; it is `append_Type_castAdd` at the underlying round index, since `ChallengeIdx.inl`
is `Fin.castAdd` on rounds. -/
theorem challenge_append_inl (i : ChallengeIdx pSpec₁) :
    (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i) = pSpec₁.Challenge i := sorry

/-- The challenge type of an appended protocol at a right-injected challenge index agrees with the
challenge type of the right component. Dually to `challenge_append_inl`, this is
`append_Type_natAdd` at the underlying round index. -/
theorem challenge_append_inr (i : ChallengeIdx pSpec₂) :
    (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i) = pSpec₂.Challenge i := sorry

/-- The challenge oracles of the left component embed into those of the appended protocol,
by reindexing along `ChallengeIdx.inl`. -/
instance subSpec_challenge_append_left :
    [pSpec₁.Challenge]ₒ ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ :=
  subSpecOfChallengeReindex ChallengeIdx.inl (challenge_append_inl (pSpec₂ := pSpec₂))

/-- The left inclusion is lawful, so lifting along it preserves the distribution and support of
challenge queries. -/
instance lawfulSubSpec_challenge_append_left :
    [pSpec₁.Challenge]ₒ ˡ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ := sorry

/-- The challenge oracles of the right component embed into those of the appended protocol,
by reindexing along `ChallengeIdx.inr`.

Note that for the degenerate `pSpec ++ₚ pSpec` both this and `subSpec_challenge_append_left` apply,
and typeclass resolution picks this one (declared later), routing challenges into the second copy.
That mirrors VCV-io's `subSpec_add_left` / `subSpec_add_right` for `spec + spec`; pass the intended
instance explicitly if the two components can coincide. -/
instance subSpec_challenge_append_right :
    [pSpec₂.Challenge]ₒ ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ :=
  subSpecOfChallengeReindex ChallengeIdx.inr (challenge_append_inr (pSpec₁ := pSpec₁))

/-- The right inclusion is lawful, so lifting along it preserves the distribution and support of
challenge queries. -/
instance lawfulSubSpec_challenge_append_right :
    [pSpec₂.Challenge]ₒ ˡ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ := sorry

/-- The two inclusions occupy disjoint parts of the appended challenge interface: a left-injected
round index is `< m` and a right-injected one is `≥ m`. This is what rules out the two components'
challenge queries aliasing each other after composition.

This records structural disjointness of the challenge inclusions, analogous to the VCV-io
instance for `spec₁ + spec₂`; ordinary append soundness uses run decomposition instead. -/
instance disjointSubSpec_challenge_append_left_right :
    OracleSpec.DisjointSubSpec
      [pSpec₁.Challenge]ₒ [pSpec₂.Challenge]ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ := sorry

/-- `disjointSubSpec_challenge_append_left_right` with the two components swapped, matching
VCV-io's pairing of `disjointSubSpec_add_left_right` / `disjointSubSpec_add_right_left`. -/
instance disjointSubSpec_challenge_append_right_left :
    OracleSpec.DisjointSubSpec
      [pSpec₂.Challenge]ₒ [pSpec₁.Challenge]ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ := sorry

variable {ι : Type} {oSpec : OracleSpec ι} {α : Type}

end Append

section SeqCompose

instance {m : ℕ} {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [inst : ∀ i, ∀ j, SampleableType ((pSpec i).Challenge j)] :
    ∀ k, SampleableType ((seqCompose pSpec).Challenge k) :=
  fun ⟨k, h⟩ => Fin.fflatten₂
    (A := Direction) (B := Type) (F := fun dir type => (h : dir = .V_to_P) → SampleableType type)
    (fun i' j' h' => inst i' ⟨j', h'⟩) k h

instance {m : ℕ} {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [inst : ∀ i, ∀ j, Inhabited ((pSpec i).Challenge j)] :
    ∀ k, Inhabited ((seqCompose pSpec).Challenge k) :=
  fun ⟨k, h⟩ => Fin.fflatten₂
    (A := Direction) (B := Type) (F := fun dir type => (h : dir = .V_to_P) → Inhabited type)
    (fun i' j' h' => inst i' ⟨j', h'⟩) k h

instance {m : ℕ} {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [inst : ∀ i, ∀ j, Fintype ((pSpec i).Challenge j)] :
    ∀ k, Fintype ((seqCompose pSpec).Challenge k) :=
  fun ⟨k, h⟩ => Fin.fflatten₂
    (A := Direction) (B := Type) (F := fun dir type => (h : dir = .V_to_P) → Fintype type)
    (fun i' j' h' => inst i' ⟨j', h'⟩) k h

/-- If all protocols' messages have oracle interfaces, then the messages of their sequential
  composition also have oracle interfaces. -/
instance {m : ℕ} {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)] :
    ∀ k, OracleInterface ((seqCompose pSpec).Message k) :=
  fun ⟨k, h⟩ => Fin.fflatten₂
    (A := Direction) (B := Type) (F := fun dir type => (h : dir = .P_to_V) → OracleInterface type)
    (fun i' j' h' => Oₘ i' ⟨j', h'⟩) k h

end SeqCompose

end ProtocolSpec
