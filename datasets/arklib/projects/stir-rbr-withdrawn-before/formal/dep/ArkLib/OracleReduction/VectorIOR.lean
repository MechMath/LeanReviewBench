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
public import dep.ToCslib.Data.PFunctor.Free.Basic
public import dep.ToMathlib.Control.OptionT
public import dep.ToMathlib.Control.WriterT
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
public import dep.VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import dep.VCVio.OracleComp.QueryTracking.Structures
public import dep.VCVio.OracleComp.QueryTracking.Tracing.Core
public import dep.VCVio.OracleComp.SimSemantics.Append.Core
public import dep.VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import dep.VCVio.OracleComp.SimSemantics.QueryImpl.Constructions.Core
public import dep.VCVio.OracleComp.SimSemantics.ReaderT.Basic
public import dep.VCVio.OracleComp.SimSemantics.SimulateQ
public import dep.VCVio.OracleComp.SimSemantics.StateT.PreservesInv
public import dep.VCVio.OracleComp.Support
public import dep.dep.CslibCompat.Basic
public import dep.dep.CslibCompat.Free

@[expose] public section

namespace ProtocolSpec

/-- The protocol specification for a V-IOR, which consists of the direction of each message and its
  length.

(assumed to be working over a fixed alphabet) -/
@[ext]
structure VectorSpec (n : ℕ) where
  dir : Fin n → Direction
  length : Fin n → Nat

namespace VectorSpec

variable {n : ℕ}

/-- Convert a `VectorSpec` into a `ProtocolSpec` for a given alphabet type `A`. The `i`-th message
  is a vector of length `vPSpec i.2` over `A`.

Note that we give the `Vector A n` type for this, instead of `Fin n → A`, for better performance in
(future) implementations. We may revisit this choice in the future. -/
@[reducible, simp]
def toProtocolSpec (A : Type) (vPSpec : VectorSpec n) : ProtocolSpec n :=
  ⟨vPSpec.dir, fun i => Vector A (vPSpec.length i)⟩

/-- The type of indices for messages in a `VectorSpec`. -/
@[reducible, inline, specialize, simp]
def MessageIdx (vPSpec : VectorSpec n) := {i : Fin n // vPSpec.dir i = .P_to_V}

/-- The type of indices for challenges in a `VectorSpec`. -/
@[reducible, inline, specialize, simp]
def ChallengeIdx (vPSpec : VectorSpec n) := {i : Fin n // vPSpec.dir i = .V_to_P}

variable {A : Type} {vPSpec : VectorSpec n}

/-- All messages in an V-IOR have the same vector oracle interface. -/
instance : OracleInterfaces (vPSpec.toProtocolSpec A) where
  oracleInterfaces := fun _ => some OracleInterface.instVector

instance : ∀ i, OracleInterface ((vPSpec.toProtocolSpec A).Message i) :=
  fun _ => OracleInterface.instVector

instance [VCVCompatible A] : ∀ i, VCVCompatible ((vPSpec.toProtocolSpec A).Challenge i) :=
  fun _ => by dsimp; infer_instance

end VectorSpec

end ProtocolSpec

variable {n : ℕ} {ι : Type}

/-- Vector Interactive Oracle Reductions.

  This is just a specialization of `OracleReduction` to the case where all messages and oracle
  statements are vectors over some alphabet, and there is no shared oracle.

  We do _not_ require the (oracle) statements and witnesses to be vectors as well, though this can
  be done if needed. -/
@[reducible]
def VectorIOR
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) (WitIn : Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) (WitOut : Type)
    (vPSpec : ProtocolSpec.VectorSpec n) (A : Type)
    [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (OStmtOut i)] :=
  OracleReduction []ₒ StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut (vPSpec.toProtocolSpec A)

/-- Vector Interactive Oracle Proofs

This is just a specialization of `OracleProof` to the case where all messages and oracle statements
are vectors over some alphabet. We do _not_ require the (oracle) statements and witnesses to be
vectors as well, though this can be done if needed. -/
@[reducible]
def VectorIOP
    (Statement : Type) {ιₛ : Type} (OStatement : ιₛ → Type) (Witness : Type)
    (vPSpec : ProtocolSpec.VectorSpec n) (A : Type)
    [∀ i, OracleInterface (OStatement i)] :=
  OracleProof []ₒ Statement OStatement Witness (vPSpec.toProtocolSpec A)

variable {n : ℕ} {vPSpec : ProtocolSpec.VectorSpec n} {A : Type}
  [SampleableType A]

open scoped NNReal

namespace VectorIOR

variable {StmtIn WitIn StmtOut WitOut : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
  [∀ i, OracleInterface (OStmtIn i)] {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
  [∀ i, OracleInterface (OStmtOut i)]

end VectorIOR

namespace VectorIOP

variable {Statement Witness : Type} {ιₛ : Type} {OStatement : ιₛ → Type}
  [∀ i, OracleInterface (OStatement i)]

/-- A vector IOP **of proximity** is **secure** with respect to completeness relation
  `completeRelation`, soundness relation `soundRelation`, and round-by-round knowledge error
  `ε_rbr` if it satisfies:
  - (perfect) completeness with respect to `completeRelation`,
  - round-by-round knowledge soundness with respect to `soundRelation` and `ε_rbr`. -/
class IsSecureWithGap
    (completeRelation : Set ((Statement × ∀ i, OStatement i) × Witness))
    (soundRelation : Set ((Statement × ∀ i, OStatement i) × Witness))
    (ε_rbr : vPSpec.ChallengeIdx → ℝ≥0)
    (vectorIOP : VectorIOP Statement OStatement Witness vPSpec A) where

  /-- The reduction is perfectly complete. -/
  is_complete : vectorIOP.perfectCompleteness (pure ()) isEmptyElim completeRelation

  /-- The reduction is round-by-round knowledge sound with respect to `relIn`, `relOut`,
    `ε_rbr`, and the state function. -/
  is_rbr_knowledge_sound :
    OracleProof.rbrKnowledgeSoundness
      (pure ()) isEmptyElim soundRelation vectorIOP.toOracleVerifier ε_rbr

end VectorIOP
