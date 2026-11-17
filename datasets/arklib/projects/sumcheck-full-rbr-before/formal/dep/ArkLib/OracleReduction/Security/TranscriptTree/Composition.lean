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
public import dep.ArkLib.OracleReduction.Security.TranscriptTree.Basic
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

namespace ChallengeTree

section AppendShape

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- Canonical arity for a challenge tree over an appended protocol. -/
def appendArity (arity₁ : pSpec₁.ChallengeIdx → ℕ) (arity₂ : pSpec₂.ChallengeIdx → ℕ) :
    (pSpec₁ ++ₚ pSpec₂).ChallengeIdx → ℕ :=
  Sum.elim arity₁ arity₂ ∘ ChallengeIdx.sumEquiv.symm

end AppendShape

end ChallengeTree

namespace ChallengeTreeShape

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- Append two protocol-generic tree shapes along sequential protocol append. -/
def append (S₁ : ChallengeTreeShape pSpec₁) (S₂ : ChallengeTreeShape pSpec₂) :
    ChallengeTreeShape (pSpec₁ ++ₚ pSpec₂) where
  arity := ChallengeTree.appendArity S₁.arity S₂.arity
  nodeOk := fun i challenges =>
    match h : ChallengeIdx.sumEquiv.symm i with
    | Sum.inl i₁ =>
        S₁.nodeOk i₁ fun j =>
          cast (sorry)
            (challenges (Fin.cast (sorry) j))
    | Sum.inr i₂ =>
        S₂.nodeOk i₂ fun j =>
          cast (sorry)
            (challenges (Fin.cast (sorry) j))

end ChallengeTreeShape

namespace ChallengeTree

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

section AppendSplit

variable {arity₁ : pSpec₁.ChallengeIdx → ℕ} {arity₂ : pSpec₂.ChallengeIdx → ℕ}

/-- Embed a right-protocol round `r : Fin (n+1)` into the appended protocol's rounds.
Reducible so that `(Fin.natAdd m i).castSucc` and `(Fin.natAdd m i).succ` reduce on the nose to
the indices `ChallengeTree` constructors produce. -/
@[reducible] def rightRound (r : Fin (n + 1)) : Fin (m + n + 1) := Fin.natAdd m r

/-- Embed a left-protocol round `r : Fin (m+1)` into the appended protocol's rounds. Written as an
explicit `Fin.mk` (defeq to `Fin.castLE`) so that `(leftRound r).val` reduces to `r.val` by
projection — important for `simp`/`Fin.snoc` lemmas in the membership proof. -/
@[reducible] def leftRound (r : Fin (m + 1)) : Fin (m + n + 1) :=
  ⟨r.val, Nat.lt_of_lt_of_le r.isLt (sorry)⟩

/-- A right-hand round of the appended protocol has `pSpec₂`'s direction. -/
theorem appendDir_right (i : Fin n) :
    (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m i) = pSpec₂.dir i := sorry

/-- A right-hand round of the appended protocol has `pSpec₂`'s type. -/
theorem appendType_right (i : Fin n) :
    (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.natAdd m i) = pSpec₂.«Type» i := sorry

/-- The appended arity at a right-hand challenge round is `arity₂`'s. -/
theorem appendArity_right {i : Fin n} {h : pSpec₂.dir i = .V_to_P}
    (hApp : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m i) = .V_to_P) :
    appendArity arity₁ arity₂ ⟨Fin.natAdd m i, hApp⟩ = arity₂ ⟨i, h⟩ := sorry

/-- Embed a `pSpec₂`-tree as the tail of a tree over the appended protocol. -/
def embedRight : {r : Fin (n + 1)} → ChallengeTree pSpec₂ arity₂ r →
    ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) (rightRound r)
  | _, .leaf => .leaf
  | _, .msgNode i h msg child =>
      have hApp : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m i) = .P_to_V :=
        (appendDir_right i).trans h
      .msgNode (Fin.natAdd m i) hApp (cast (appendType_right i).symm msg) (embedRight child)
  | _, .chalNode i h chals children =>
      have hApp : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m i) = .V_to_P :=
        (appendDir_right i).trans h
      have hAr : appendArity arity₁ arity₂ ⟨Fin.natAdd m i, hApp⟩ = arity₂ ⟨i, h⟩ :=
        appendArity_right hApp
      .chalNode (Fin.natAdd m i) hApp
        (fun j => cast (appendType_right i).symm (chals (Fin.cast hAr j)))
        (fun j => embedRight (children (Fin.cast hAr j)))

/-- Index bookkeeping: the successor of a right-hand round, as a raw-`ℕ` round equation. -/
theorem rightSucc {i : Fin (m + n)} {rv : ℕ} (hv : (i : ℕ) = m + rv) (hlt : rv + 1 < n + 1) :
    i.succ = rightRound ⟨rv + 1, hlt⟩ := sorry

/-- Read a `pSpec₂`-tree off an appended tree that has already entered the right protocol.

The round is passed as a raw `ℕ` (`rv`) plus its bound, so the index equations of the
`ChallengeTree` constructors hold definitionally and no `Fin.lastCases` motive, `▸` or `convert` is
needed — see this file's `## Implementation`. -/
def unembedRight : {a : Fin (m + n + 1)} →
    ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) a →
    (rv : ℕ) → (hlt : rv < n + 1) → a = rightRound ⟨rv, hlt⟩ →
    ChallengeTree pSpec₂ arity₂ ⟨rv, hlt⟩
  | _, .leaf, rv, hlt, h => by
      obtain rfl : rv = n := sorry
      exact .leaf
  | _, .msgNode i hd msg child, rv, hlt, h =>
      have hv : (i : ℕ) = m + rv := sorry
      have hrn : rv < n := sorry
      have hi : i = Fin.natAdd m (⟨rv, hrn⟩ : Fin n) := Fin.ext (sorry)
      have hdir : pSpec₂.dir ⟨rv, hrn⟩ = .P_to_V := sorry
      .msgNode ⟨rv, hrn⟩ hdir (cast (sorry) msg)
        (unembedRight child (rv + 1) (sorry) (rightSucc hv (sorry)))
  | _, .chalNode i hd chals children, rv, hlt, h =>
      have hv : (i : ℕ) = m + rv := sorry
      have hrn : rv < n := sorry
      have hi : i = Fin.natAdd m (⟨rv, hrn⟩ : Fin n) := Fin.ext (sorry)
      have hdir : pSpec₂.dir ⟨rv, hrn⟩ = .V_to_P := sorry
      have hAr : appendArity arity₁ arity₂ ⟨i, hd⟩ = arity₂ ⟨⟨rv, hrn⟩, hdir⟩ := sorry
      .chalNode ⟨rv, hrn⟩ hdir
        (fun j => cast (sorry) (chals (Fin.cast hAr.symm j)))
        (fun j => unembedRight (children (Fin.cast hAr.symm j)) (rv + 1) (sorry)
          (rightSucc hv (sorry)))

/-- A split certificate for the first `m` rounds. At the boundary it stores the suffix tree itself;
before that it mirrors the appended tree's left-protocol structure. -/
inductive SplitData
    (arity₁ : pSpec₁.ChallengeIdx → ℕ) (arity₂ : pSpec₂.ChallengeIdx → ℕ) :
    Fin (m + 1) → Type where
  | boundary (t₂ : ChallengeTree pSpec₂ arity₂ (0 : Fin (n + 1))) :
      SplitData arity₁ arity₂ (Fin.last m)
  | msg (i : Fin m) (h : pSpec₁.dir i = .P_to_V) (msg : pSpec₁.Message ⟨i, h⟩)
      (child : SplitData arity₁ arity₂ i.succ) : SplitData arity₁ arity₂ i.castSucc
  | chal (i : Fin m) (h : pSpec₁.dir i = .V_to_P)
      (challenges : Fin (arity₁ ⟨i, h⟩) → pSpec₁.Challenge ⟨i, h⟩)
      (children : Fin (arity₁ ⟨i, h⟩) → SplitData arity₁ arity₂ i.succ) :
      SplitData arity₁ arity₂ i.castSucc

/-- The first-stage tree projected from a `SplitData` certificate. -/
def SplitData.fst {r : Fin (m + 1)} : SplitData arity₁ arity₂ r →
    ChallengeTree pSpec₁ arity₁ r
  | .boundary _ => .leaf
  | .msg _ h m₁ child => .msgNode _ h m₁ child.fst
  | .chal _ h challenges children => .chalNode _ h challenges fun j => (children j).fst

/-- The appended source tree represented by a `SplitData` certificate. Every constructor index
lands on the nose (`leftRound` reducible); the boundary reuses `embedRight` since
`leftRound (Fin.last m)` is defeq `rightRound 0`. -/
def SplitData.src : {r : Fin (m + 1)} → SplitData arity₁ arity₂ r →
    ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) (leftRound r)
  | _, .boundary t₂ => embedRight t₂
  | _, .msg i h m₁ child =>
      have hApp : (pSpec₁ ++ₚ pSpec₂).dir (Fin.castAdd n i) = .P_to_V := sorry
      .msgNode (Fin.castAdd n i) hApp
        (cast (sorry) m₁)
        child.src
  | _, .chal i h challenges children =>
      have hApp : (pSpec₁ ++ₚ pSpec₂).dir (Fin.castAdd n i) = .V_to_P := sorry
      have hIdx : (⟨Fin.castAdd n i, hApp⟩ : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx)
          = ChallengeIdx.inl ⟨i, h⟩ := sorry
      have hAr : appendArity arity₁ arity₂ ⟨Fin.castAdd n i, hApp⟩ = arity₁ ⟨i, h⟩ := sorry
      .chalNode (Fin.castAdd n i) hApp
        (fun j => cast (sorry)
          (challenges (Fin.cast hAr j)))
        (fun j => (children (Fin.cast hAr j)).src)

/-- Peel the child path from a `LeafPath` at a message node, bundled with the reconstruction
`p = .msg p'`.

Inverting a `LeafPath` at a fixed `castSucc`-indexed tree fails (the round equation `↑k = m'` is
unsolvable for `cases`), so the round and tree stay general and the cases are routed by the
hypotheses `ρ = k.castSucc` and `HEq T (.msgNode …)`. This is a plain `match` — note there is no
recursion here at all, and hence no termination obligation. -/
def peelMsgAux : {ρ : Fin (m + 1)} → {T : ChallengeTree pSpec₁ arity₁ ρ} → (p : LeafPath T) →
    (k : Fin m) → (h : pSpec₁.dir k = .P_to_V) → (msg : pSpec₁.Message ⟨k, h⟩) →
    (child : ChallengeTree pSpec₁ arity₁ k.succ) →
    ρ = k.castSucc → HEq T (ChallengeTree.msgNode k h msg child) →
    { p' : LeafPath child // HEq p (@LeafPath.msg _ _ _ k h msg child p') }
  | _, _, .leaf, k, _, _, _, hρ, _ => by
      exfalso
      have hv := congrArg Fin.val hρ
      simp only [Fin.val_last, Fin.val_castSucc] at hv
      have := k.isLt; omega
  | _, _, @LeafPath.msg _ _ _ k' _ _ _ path, k, h, msg, child, hρ, hT => by
      obtain rfl : k' = k := Fin.castSucc_injective _ hρ
      injection eq_of_heq hT with _ hmsg hchild
      subst hmsg; subst hchild
      exact ⟨path, HEq.rfl⟩
  | _, _, @LeafPath.chal _ _ _ k' _ _ _ _ _, k, h, msg, child, hρ, hT => by
      obtain rfl : k' = k := Fin.castSucc_injective _ hρ
      exact absurd (eq_of_heq hT) (sorry)

/-- The child path obtained by peeling a `LeafPath` at a message node (the bundled certificate
`peelMsgAux` dropped to its underlying path). -/
def peelMsg {k : Fin m} {h : pSpec₁.dir k = .P_to_V} {msg : pSpec₁.Message ⟨k, h⟩}
    {child : ChallengeTree pSpec₁ arity₁ k.succ} (p : LeafPath (.msgNode k h msg child)) :
    LeafPath child := (peelMsgAux p k h msg child rfl HEq.rfl).1

/-- Peel the branch index and child path from a `LeafPath` at a challenge node, bundled with the
reconstruction `p = .chal j p'`. Non-recursive, like `peelMsgAux`. -/
def chalPeelAux : {ρ : Fin (m + 1)} → {T : ChallengeTree pSpec₁ arity₁ ρ} → (p : LeafPath T) →
    (k : Fin m) → (h : pSpec₁.dir k = .V_to_P) →
    (challenges : Fin (arity₁ ⟨k, h⟩) → pSpec₁.Challenge ⟨k, h⟩) →
    (children : Fin (arity₁ ⟨k, h⟩) → ChallengeTree pSpec₁ arity₁ k.succ) →
    ρ = k.castSucc → HEq T (ChallengeTree.chalNode k h challenges children) →
    { jp : (j : Fin (arity₁ ⟨k, h⟩)) × LeafPath (children j) //
      HEq p (@LeafPath.chal _ _ _ k h challenges children jp.1 jp.2) }
  | _, _, .leaf, k, _, _, _, hρ, _ => by
      exfalso
      have hv := congrArg Fin.val hρ
      simp only [Fin.val_last, Fin.val_castSucc] at hv
      have := k.isLt; omega
  | _, _, @LeafPath.msg _ _ _ k' _ _ _ _, k, h, challenges, children, hρ, hT => by
      obtain rfl : k' = k := Fin.castSucc_injective _ hρ
      exact absurd (eq_of_heq hT) (sorry)
  | _, _, @LeafPath.chal _ _ _ k' _ _ _ j path, k, h, challenges, children, hρ, hT => by
      obtain rfl : k' = k := Fin.castSucc_injective _ hρ
      injection eq_of_heq hT with _ hchal hchildren
      subst hchal; subst hchildren
      exact ⟨⟨j, path⟩, HEq.rfl⟩

/-- The branch index and child path obtained by peeling a `LeafPath` at a challenge node (the
bundled certificate `chalPeelAux` dropped to its underlying index/path pair). -/
def chalPeel {k : Fin m} {h : pSpec₁.dir k = .V_to_P}
    {challenges : Fin (arity₁ ⟨k, h⟩) → pSpec₁.Challenge ⟨k, h⟩}
    {children : Fin (arity₁ ⟨k, h⟩) → ChallengeTree pSpec₁ arity₁ k.succ}
    (p : LeafPath (.chalNode k h challenges children)) :
    (j : Fin (arity₁ ⟨k, h⟩)) × LeafPath (children j) :=
  (chalPeelAux p k h challenges children rfl HEq.rfl).1

/-- The second-stage suffix tree selected below a given first-stage leaf path. Following the path
down the certificate, the boundary hands back the suffix tree it stores; message and challenge nodes
recurse into the peeled child certificate. -/
def SplitData.sndAt {r : Fin (m + 1)} :
    (S : SplitData arity₁ arity₂ r) → LeafPath S.fst → ChallengeTree pSpec₂ arity₂ 0
  | .boundary t₂, _ => t₂
  | .msg _ _ _ child, path => child.sndAt (peelMsg path)
  | .chal _ _ _ children, path => (children (chalPeel path).1).sndAt (chalPeel path).2

/-- Index bookkeeping: the successor of a left-hand round, as a raw-`ℕ` round equation. -/
theorem leftSucc {i : Fin (m + n)} {rv : ℕ} (hv : (i : ℕ) = rv) (hlt : rv + 1 < m + 1) :
    i.succ = leftRound ⟨rv + 1, hlt⟩ := sorry

/-- At the boundary round (`a` is round `m` of the appended protocol) the tree has already entered
the right protocol, so `unembedRight` reads it off directly. Kept as a named definition so that the
three boundary branches of `splitOf` share one proof obligation, and so elaboration can infer
`pSpec₁`/`arity₁` from the argument's type. -/
def boundaryOf {a : Fin (m + n + 1)}
    (t : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) a)
    (hb : (a : ℕ) = m) : SplitData arity₁ arity₂ (Fin.last m) :=
  .boundary (unembedRight t 0 (sorry) (Fin.ext (sorry)))

/-- Build the split certificate for an appended tree at left round `rv`.

Boundary detection is a plain `dite` on `rv < m` — no `Fin.lastCases` motive — and every
constructor lands on its index without transport, because the round travels as a raw `ℕ`. -/
def splitOf : {a : Fin (m + n + 1)} →
    ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) a →
    (rv : ℕ) → (hlt : rv < m + 1) → a = leftRound ⟨rv, hlt⟩ → SplitData arity₁ arity₂ ⟨rv, hlt⟩
  | _, .leaf, rv, hlt, h => by
      have hv : m + n = rv := by
        have hv := congrArg Fin.val h; simpa [leftRound] using hv
      obtain rfl : rv = m := sorry
      exact boundaryOf .leaf (sorry)
  | _, .msgNode i hd msg child, rv, hlt, h =>
      have hv : (i : ℕ) = rv := sorry
      if hrm : rv < m then
        have hi : i = Fin.castAdd n (⟨rv, hrm⟩ : Fin m) := Fin.ext (sorry)
        have hdir : pSpec₁.dir ⟨rv, hrm⟩ = .P_to_V := sorry
        .msg ⟨rv, hrm⟩ hdir (cast (sorry) msg)
          (splitOf child (rv + 1) (sorry) (leftSucc hv (sorry)))
      else by
        obtain rfl : rv = m := sorry
        exact boundaryOf (.msgNode i hd msg child) (sorry)
  | _, .chalNode i hd chals children, rv, hlt, h =>
      have hv : (i : ℕ) = rv := sorry
      if hrm : rv < m then
        have hi : i = Fin.castAdd n (⟨rv, hrm⟩ : Fin m) := Fin.ext (sorry)
        have hdir : pSpec₁.dir ⟨rv, hrm⟩ = .V_to_P := sorry
        have hAr : appendArity arity₁ arity₂ ⟨i, hd⟩ = arity₁ ⟨⟨rv, hrm⟩, hdir⟩ := sorry
        .chal ⟨rv, hrm⟩ hdir
          (fun j => cast (sorry) (chals (Fin.cast hAr.symm j)))
          (fun j => splitOf (children (Fin.cast hAr.symm j)) (rv + 1) (sorry)
            (leftSucc hv (sorry)))
      else by
        obtain rfl : rv = m := sorry
        exact boundaryOf (.chalNode i hd chals children)
          (sorry)

/-- Build a `SplitData` certificate from an appended tree. -/
def splitDataOfTree {r : Fin (m + 1)}
    (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) (leftRound r)) :
    SplitData arity₁ arity₂ r := splitOf T r.val r.isLt rfl

/-- The `SplitData` certificate built from an appended tree faithfully represents it. -/
theorem splitDataOfTree_src {r : Fin (m + 1)}
    (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) (leftRound r)) :
    (splitDataOfTree (arity₁ := arity₁) (arity₂ := arity₂) T).src = T := sorry

section Structure

variable {S₁ : ChallengeTreeShape pSpec₁} {S₂ : ChallengeTreeShape pSpec₂}

end Structure

/-- A split of a challenge tree over an appended protocol into a first-stage tree and a suffix tree
below every first-stage leaf. -/
structure AppendSplit
    (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) 0) where
  /-- The projected first-stage tree. -/
  fst : ChallengeTree pSpec₁ arity₁ 0
  /-- The second-stage suffix tree below a first-stage leaf. -/
  sndAt : LeafPath fst → ChallengeTree pSpec₂ arity₂ 0

/-- Split a tree over an appended protocol into a first-stage tree and path-indexed suffix trees. -/
def appendSplit
    (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) 0) :
      AppendSplit T where
  fst := (splitDataOfTree (r := 0) T).fst
  sndAt := (splitDataOfTree (r := 0) T).sndAt

variable {S₁ : ChallengeTreeShape pSpec₁} {S₂ : ChallengeTreeShape pSpec₂}

section Membership

end Membership

section LeafPathGlue

/-- Embed a leaf path of a `pSpec₂`-tree into the `embedRight`-embedded appended tree: past the
boundary an appended tree *is* a `pSpec₂` tree, and this is that fact for paths. The branch index at
a challenge node is transported along `appendArity_right`, exactly as `embedRight` transports the
children it indexes. -/
def LeafPath.embedRight : {r : Fin (n + 1)} → {t : ChallengeTree pSpec₂ arity₂ r} →
    LeafPath t → LeafPath (ChallengeTree.embedRight (arity₁ := arity₁) t)
  | _, _, .leaf => .leaf
  | _, _, .msg p => .msg p.embedRight
  | _, .chalNode i h _ _, .chal j p =>
      .chal (Fin.cast (appendArity_right (arity₁ := arity₁) (h := h)
        ((appendDir_right i).trans h)).symm j) p.embedRight

/-- Glue a first-stage leaf path with a suffix leaf path into a leaf path of the source tree. The
recursion follows the certificate: at the boundary the suffix path is embedded
(`LeafPath.embedRight`), and message/challenge nodes rebuild the node around the glue of the peeled
child path. -/
def SplitData.gluePath : {r : Fin (m + 1)} → (S : SplitData arity₁ arity₂ r) →
    (p₁ : LeafPath S.fst) → LeafPath (S.sndAt p₁) → LeafPath S.src
  | _, .boundary _, _, p₂ => p₂.embedRight
  | _, .msg _ _ _ child, p₁, p₂ => .msg (child.gluePath (peelMsg p₁) p₂)
  | _, .chal i h _ children, p₁, p₂ =>
      have hApp : (pSpec₁ ++ₚ pSpec₂).dir (Fin.castAdd n i) = .V_to_P := sorry
      have hAr : appendArity arity₁ arity₂ ⟨Fin.castAdd n i, hApp⟩ = arity₁ ⟨i, h⟩ := sorry
      .chal (Fin.cast hAr.symm (chalPeel p₁).1)
        ((children (chalPeel p₁).1).gluePath (chalPeel p₁).2 p₂)

/-- Transport a leaf path along an equality of trees. Needed once, to move the glue built over a
certificate's `src` onto the tree the certificate was read from (`splitDataOfTree_src`). -/
def LeafPath.transport {r : Fin (m + 1)} {T T' : ChallengeTree pSpec₁ arity₁ r}
    (h : T = T') (p : LeafPath T) : LeafPath T' := h ▸ p

/-- Path-level recombination for `appendSplit`: the leaf path of `T` selected by a first-stage leaf
path together with a leaf path of the suffix tree below it. -/
def AppendSplit.gluePath
    (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) 0)
    (p₁ : LeafPath T.appendSplit.fst) (p₂ : LeafPath (T.appendSplit.sndAt p₁)) : LeafPath T :=
  ((splitDataOfTree (r := 0) T).gluePath p₁ p₂).transport
    (splitDataOfTree_src (r := 0) (arity₁ := arity₁) (arity₂ := arity₂) T)

end LeafPathGlue

section EscapeEventAppend

variable {arity₁ : pSpec₁.ChallengeIdx → ℕ} {arity₂ : pSpec₂.ChallengeIdx → ℕ}

/-- Binary composition of escape events along a protocol append: the composed event fires iff the
left event fires on the prefix tree, or the right event fires on the suffix tree hanging off some
prefix leaf, at the intermediate statement `verify₁` computes on that leaf's transcript. Each
factor's event stays self-contained, so factors may track breaks of entirely different assumptions.

Where `verify₁` is unconstrained the composed event evaluates `esc₂` at intermediate statements no
honest execution produces — harmless, since an honest event is a break at *every* `(stmt, tree)`
pair (`ChallengeTree.EscapeEvent`). -/
def EscapeEvent.append {Stmt₁ Stmt₂ : Type}
    (esc₁ : EscapeEvent Stmt₁ pSpec₁ arity₁) (esc₂ : EscapeEvent Stmt₂ pSpec₂ arity₂)
    (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂) :
    EscapeEvent Stmt₁ (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) :=
  fun stmt tree =>
    esc₁ stmt tree.appendSplit.fst ∨
    ∃ path : LeafPath tree.appendSplit.fst,
      esc₂ (verify₁ stmt path.fullTranscript) (tree.appendSplit.sndAt path)

end EscapeEventAppend

end AppendSplit

end ChallengeTree

end ProtocolSpec

namespace Extractor

open ProtocolSpec ProtocolSpec.ChallengeTree

variable {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  {arity₁ : pSpec₁.ChallengeIdx → ℕ} {arity₂ : pSpec₂.ChallengeIdx → ℕ}

/-- **Sequential composition of witness-only tree extractors.** Split the appended tree
(`ChallengeTree.appendSplit`) and run the left extractor on the prefix tree, feeding it — per prefix
leaf — the right extractor's output on the suffix tree hanging below that leaf. The intermediate
statement the right extractor runs at is computed by `verify₁`, the **left verifier's verdict
function**, passed as data; a package reads it off its `Verifier.PureForm` / `Verifier.GuardedForm`
field, which is exactly why those fields carry the verdict as data rather than as an existential.

The right extractor's own witnessing input is the top-level witnessing read at the glued path
(`ChallengeTree.AppendSplit.gluePath`), and that glue is the *only* path machinery a composed
extraction runs: extractors attribute no output statements, so nothing ever un-glues a path.
Declining propagates — if the top witnessing declines at some glued leaf the right extractor may
decline, hence so may the left. -/
def TreeBased.append (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : TreeBased Stmt₁ Wit₁ Wit₂ pSpec₁ arity₁)
    (E₂ : TreeBased Stmt₂ Wit₂ Wit₃ pSpec₂ arity₂) :
    TreeBased Stmt₁ Wit₁ Wit₃ (pSpec₁ ++ₚ pSpec₂) (ChallengeTree.appendArity arity₁ arity₂) :=
  fun stmt tree o =>
    E₁ stmt tree.appendSplit.fst fun p₁ =>
      E₂ (verify₁ stmt p₁.fullTranscript) (tree.appendSplit.sndAt p₁)
        fun p₂ => o (ChallengeTree.AppendSplit.gluePath tree p₁ p₂)

end Extractor
