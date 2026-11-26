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

open OracleSpec OracleComp PFunctor

/-- A lens for transporting input and output statements for the verifier of a (non-oracle)
    reduction.

  Consists of two functions:
  - `proj : OuterStmtIn → InnerStmtIn` : Transport input statements from the outer context to
    the inner context
  - `lift : OuterStmtIn → InnerStmtOut → OuterStmtOut` : Transport output statements from the
    inner context to the outer context, additionally relying on the outer input statement.

  This is exactly the same as a `PFunctor.Lens` between two monomials defined by the input and
  output statements (from the outer to the inner context).
-/
@[inline, reducible]
def Statement.Lens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type) :=
  PFunctor.Lens (OuterStmtIn X^ OuterStmtOut) (InnerStmtIn X^ InnerStmtOut)

namespace Statement.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
  (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)

/-- Transport input statements from the outer context to the inner context -/
@[inline, reducible]
def proj : OuterStmtIn → InnerStmtIn :=
  lens.toFunA

/-- Transport output statements from the inner context to the outer context,
  additionally relying on the input statements of the outer context. -/
@[inline, reducible]
def lift : OuterStmtIn → InnerStmtOut → OuterStmtOut :=
  lens.toFunB

end Statement.Lens

/-- A lens for transporting input and output statements (both oracle and non-oracle) for the
  oracle verifier of an oracle reduction.

  TODO: figure out the right way to define this -/
@[inline, reducible]
def OracleStatement.Lens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
    {Outer_ιₛᵢ : Type} (OuterOStmtIn : Outer_ιₛᵢ → Type) [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} (OuterOStmtOut : Outer_ιₛₒ → Type) [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} (InnerOStmtIn : Inner_ιₛᵢ → Type) [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} (InnerOStmtOut : Inner_ιₛₒ → Type)
    [∀ i, OracleInterface (InnerOStmtOut i)] :=
    Statement.Lens (OuterStmtIn × ∀ i, OuterOStmtIn i) (OuterStmtOut × ∀ i, OuterOStmtOut i)
                  (InnerStmtIn × ∀ i, InnerOStmtIn i) (InnerStmtOut × ∀ i, InnerOStmtOut i)

namespace OracleStatement.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
    (lens : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut)

/-- Transport input statements from the outer context to the inner context

TODO: refactor etc. -/
@[inline, reducible]
def proj : OuterStmtIn × (∀ i, OuterOStmtIn i) → InnerStmtIn × (∀ i, InnerOStmtIn i) :=
  lens.toFunA

/-- Transport output statements from the inner context to the outer context,
  additionally relying on the input statements of the outer context.

  TODO: refactor etc. -/
@[inline, reducible]
def lift : OuterStmtIn × (∀ i, OuterOStmtIn i) → InnerStmtOut × (∀ i, InnerOStmtOut i) →
    OuterStmtOut × (∀ i, OuterOStmtOut i) :=
  lens.toFunB

end OracleStatement.Lens

/-- A query-realizable lens between oracle statements.

Input-oracle projection may depend on the explicit outer input statement.
Output-oracle lifting is deliberately statement-independent: this is the
condition needed for output-oracle simulations to remain composable without
materializing intermediate verifier statements. -/
structure OracleStatement.ExecutableLens
    (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
    {Outer_ιₛᵢ : Type} (OuterOStmtIn : Outer_ιₛᵢ → Type)
    [OuterOᵢ : ∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} (OuterOStmtOut : Outer_ιₛₒ → Type)
    [OuterOₒ : ∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} (InnerOStmtIn : Inner_ιₛᵢ → Type)
    [InnerOᵢ : ∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} (InnerOStmtOut : Inner_ιₛₒ → Type)
    [InnerOₒ : ∀ i, OracleInterface (InnerOStmtOut i)] where
  /-- Project the explicit input statement. -/
  projStmt : OuterStmtIn → InnerStmtIn
  /-- Materialized input-oracle projection, used by relation-facing semantics. -/
  materializeInput : OuterStmtIn →
    (∀ i, OuterOStmtIn i) → ∀ i, InnerOStmtIn i
  /-- Query-by-query implementation of the input-oracle projection. -/
  simulateInput : OuterStmtIn →
    QueryImpl [InnerOStmtIn]ₒ (OracleComp [OuterOStmtIn]ₒ)
  /-- The input query implementation agrees with the materialized projection. -/
  simulateInput_eq : ∀ outerStmt outerOStmt q,
    simulateQ (OracleInterface.simOracle0 OuterOStmtIn outerOStmt)
        (simulateInput outerStmt q) =
      (InnerOᵢ q.1).answer (materializeInput outerStmt outerOStmt q.1) q.2
  /-- Lift the explicit output statement. -/
  liftStmt : OuterStmtIn → InnerStmtOut → OuterStmtOut
  /-- Materialized output-oracle lift, used by relation-facing semantics. -/
  materializeOutput : (∀ i, OuterOStmtIn i) →
    (∀ i, InnerOStmtOut i) → ∀ i, OuterOStmtOut i
  /-- Query-by-query implementation of the output-oracle lift. -/
  simulateOutput :
    QueryImpl [OuterOStmtOut]ₒ (OracleComp ([OuterOStmtIn]ₒ + [InnerOStmtOut]ₒ))
  /-- The output query implementation agrees with the materialized lift. -/
  simulateOutput_eq : ∀ outerOStmt innerOStmt q,
    simulateQ
        (QueryImpl.add (OracleInterface.simOracle0 OuterOStmtIn outerOStmt)
          (OracleInterface.simOracle0 InnerOStmtOut innerOStmt))
        (simulateOutput q) =
      (OuterOₒ q.1).answer (materializeOutput outerOStmt innerOStmt q.1) q.2

namespace OracleStatement.ExecutableLens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type}
    [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type}
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type}
    [∀ i, OracleInterface (InnerOStmtOut i)]

/-- Forget query implementations and retain the extensional statement lens. -/
@[reducible]
def toLens (lens : OracleStatement.ExecutableLens
    OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
    OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut) :
    OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut where
  toFunA := fun ⟨stmt, oStmt⟩ ↦
    ⟨lens.projStmt stmt, lens.materializeInput stmt oStmt⟩
  toFunB := fun ⟨stmt, oStmt⟩ ⟨stmtOut, oStmtOut⟩ ↦
    ⟨lens.liftStmt stmt stmtOut, lens.materializeOutput oStmt oStmtOut⟩

end OracleStatement.ExecutableLens

/-- Lenses for transporting the input & output witnesses from an inner protocol to an outer
    protocol.

  It consists of two functions:
  - `projWit : OuterStmtIn × OuterWitIn → InnerWitIn`, which derives the inner input witness from
    the outer one, requiring also the outer input statement.
  - `liftWit : OuterStmtIn × OuterWitIn → InnerStmtOut × InnerWitOut → OuterWitOut`, which
    derives the outer output witness from outer input witness & the inner output one, requiring
    also the associated statements.

  The inclusion of the statements are necessary when we consider the full view of the prover. In
  practice as well, oftentimes a lens between only witnesses are not enough. -/
@[inline, reducible]
def Witness.Lens
    (OuterStmtIn InnerStmtOut OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) :=
  PFunctor.Lens ((OuterStmtIn × OuterWitIn) X^ OuterWitOut)
    (InnerWitIn X^ (InnerStmtOut × InnerWitOut))

namespace Witness.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
          OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (lens : Witness.Lens OuterStmtIn InnerStmtOut OuterWitIn OuterWitOut InnerWitIn InnerWitOut)

/-- Transport input witness from the outer context to the inner context -/
@[inline, reducible]
def proj : OuterStmtIn × OuterWitIn → InnerWitIn :=
  lens.toFunA

/-- Transport output witness from the inner context to the outer context,
  additionally relying on the input statements of the outer context. -/
@[inline, reducible]
def lift : OuterStmtIn × OuterWitIn → InnerStmtOut × InnerWitOut → OuterWitOut :=
  lens.toFunB

end Witness.Lens

/-- A structure collecting a lens for the prover, and a lens for the verifier, for transporting
  between the contexts of an outer reduction and an inner reduction. -/
structure Context.Lens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                          OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) where
  stmt : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
  wit : Witness.Lens OuterStmtIn InnerStmtOut OuterWitIn OuterWitOut InnerWitIn InnerWitOut

namespace Context.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
          OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                OuterWitIn OuterWitOut InnerWitIn InnerWitOut)

/-- Projection of the context. -/
@[inline, reducible]
def proj : OuterStmtIn × OuterWitIn → InnerStmtIn × InnerWitIn :=
  fun ctxIn => ⟨lens.stmt.toFunA ctxIn.1, lens.wit.toFunA ctxIn⟩

/-- Lifting of the context. -/
@[inline, reducible]
def lift : OuterStmtIn × OuterWitIn → InnerStmtOut × InnerWitOut → OuterStmtOut × OuterWitOut :=
  fun ctxIn ctxOut =>
    ⟨lens.stmt.toFunB ctxIn.1 ctxOut.1, lens.wit.toFunB ctxIn ctxOut⟩

end Context.Lens

/-- A structure collecting a lens for the prover, and a lens for the oracle verifier, for
  transporting between the contexts of an outer oracle reduction and an inner oracle reduction. -/
structure OracleContext.Lens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
    {Outer_ιₛᵢ : Type} (OuterOStmtIn : Outer_ιₛᵢ → Type) [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} (OuterOStmtOut : Outer_ιₛₒ → Type) [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} (InnerOStmtIn : Inner_ιₛᵢ → Type) [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} (InnerOStmtOut : Inner_ιₛₒ → Type) [∀ i, OracleInterface (InnerOStmtOut i)]
    (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) where
  stmt : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                  OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
  wit : Witness.Lens (OuterStmtIn × ∀ i, OuterOStmtIn i) (InnerStmtOut × ∀ i, InnerOStmtOut i)
                          OuterWitIn OuterWitOut InnerWitIn InnerWitOut

namespace OracleContext.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                    OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                                    OuterWitIn OuterWitOut InnerWitIn InnerWitOut)

/-- Projection of the context. -/
@[inline, reducible]
def proj : (OuterStmtIn × (∀ i, OuterOStmtIn i)) × OuterWitIn →
    (InnerStmtIn × (∀ i, InnerOStmtIn i)) × InnerWitIn :=
  fun ctxIn => ⟨lens.stmt.proj ctxIn.1, lens.wit.proj ctxIn⟩

/-- Lifting of the context. -/
@[inline, reducible]
def lift : (OuterStmtIn × (∀ i, OuterOStmtIn i)) × OuterWitIn →
    (InnerStmtOut × (∀ i, InnerOStmtOut i)) × InnerWitOut →
    (OuterStmtOut × (∀ i, OuterOStmtOut i)) × OuterWitOut :=
  fun ctxIn ctxOut => ⟨lens.stmt.lift ctxIn.1 ctxOut.1, lens.wit.lift ctxIn ctxOut⟩

/-- Convert the oracle context lens to a context lens. -/
@[inline, reducible]
def toContext :
    Context.Lens (OuterStmtIn × (∀ i, OuterOStmtIn i)) (OuterStmtOut × (∀ i, OuterOStmtOut i))
                (InnerStmtIn × (∀ i, InnerOStmtIn i)) (InnerStmtOut × (∀ i, InnerOStmtOut i))
                OuterWitIn OuterWitOut InnerWitIn InnerWitOut :=
  ⟨lens.stmt, lens.wit⟩

end OracleContext.Lens

/-- An oracle-context lens whose statement component is executable by
querying, together with the ordinary witness lens used by the prover. -/
structure OracleContext.ExecutableLens
    (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
    {Outer_ιₛᵢ : Type} (OuterOStmtIn : Outer_ιₛᵢ → Type)
    [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} (OuterOStmtOut : Outer_ιₛₒ → Type)
    [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} (InnerOStmtIn : Inner_ιₛᵢ → Type)
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} (InnerOStmtOut : Inner_ιₛₒ → Type)
    [∀ i, OracleInterface (InnerOStmtOut i)]
    (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) where
  stmt : OracleStatement.ExecutableLens
    OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
    OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
  wit : Witness.Lens (OuterStmtIn × ∀ i, OuterOStmtIn i)
    (InnerStmtOut × ∀ i, InnerOStmtOut i)
    OuterWitIn OuterWitOut InnerWitIn InnerWitOut

namespace OracleContext.ExecutableLens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type}
    [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type}
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type}
    [∀ i, OracleInterface (InnerOStmtOut i)]
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}

/-- Forget the executable implementations and retain the extensional oracle
context lens. -/
@[reducible]
def toLens (lens : OracleContext.ExecutableLens
    OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
    OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
    OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :
    OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut where
  stmt := lens.stmt.toLens
  wit := lens.wit

end OracleContext.ExecutableLens

/-- Lens for lifting the witness extraction procedure from the inner reduction to the outer
  reduction.

This goes in the reverse direction (output to input) compared to the witness lens for the prover,
and requires in addition the outer input statement.
-/
@[inline, reducible]
def Witness.InvLens (OuterStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) :=
  PFunctor.Lens ((OuterStmtIn × OuterWitOut) X^ OuterWitIn) (InnerWitOut X^ InnerWitIn)

namespace Witness.InvLens

variable {OuterStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
  (lens : Witness.InvLens OuterStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut)

/-- Projection of the witness. -/
@[inline, reducible]
def proj : OuterStmtIn × OuterWitOut → InnerWitOut :=
  lens.toFunA

/-- Lifting of the witness. -/
@[inline, reducible]
def lift : OuterStmtIn × OuterWitOut → InnerWitIn → OuterWitIn :=
  lens.toFunB

end Witness.InvLens

/-- Lens for lifting the extractor from the inner reduction to the outer reduction.

This consists of two components:
- `stmt` : the statement lens
- `wit` : the witness lens in the reverse direction, matching the input-output interface of the
  extractor, i.e. `StmtIn × WitOut → WitIn` (ignoring transcript and query logs)
-/
@[ext]
structure Extractor.Lens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                          OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) where
  stmt : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
  wit : Witness.InvLens OuterStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut

namespace Extractor.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
          OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                OuterWitIn OuterWitOut InnerWitIn InnerWitOut)

/-- Transport the tuple of (input statement, output witness) from the outer context to the inner
  context -/
@[inline, reducible]
def proj (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
    OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :
    OuterStmtIn × OuterWitOut → InnerStmtIn × InnerWitOut :=
  fun ⟨stmtIn, witOut⟩ => ⟨lens.stmt.proj stmtIn, lens.wit.proj (stmtIn, witOut)⟩

end Extractor.Lens

/-- Conditions for the lens / transformation to preserve completeness

For `lift`, we require compatibility relations between the outer input statement/witness and
the inner output statement/witness -/
class Context.Lens.IsComplete {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (outerRelIn : Set (OuterStmtIn × OuterWitIn))
    (innerRelIn : Set (InnerStmtIn × InnerWitIn))
    (outerRelOut : Set (OuterStmtOut × OuterWitOut))
    (innerRelOut : Set (InnerStmtOut × InnerWitOut))
    (compat : (OuterStmtIn × OuterWitIn) → (InnerStmtOut × InnerWitOut) → Prop)
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut) where

  proj_complete : ∀ stmtIn witIn,
    (stmtIn, witIn) ∈ outerRelIn →
    (lens.stmt.proj stmtIn, lens.wit.proj (stmtIn, witIn)) ∈ innerRelIn

  lift_complete : ∀ outerStmtIn outerWitIn innerStmtOut innerWitOut,
    compat (outerStmtIn, outerWitIn) (innerStmtOut, innerWitOut) →
    (outerStmtIn, outerWitIn) ∈ outerRelIn →
    (innerStmtOut, innerWitOut) ∈ innerRelOut →
    (lens.stmt.lift outerStmtIn innerStmtOut,
    lens.wit.lift (outerStmtIn, outerWitIn) (innerStmtOut, innerWitOut)) ∈ outerRelOut

/-- The completeness condition for the oracle context lens is just the one for the underlying
  context lens -/
@[reducible, simp]
def OracleContext.Lens.IsComplete {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (outerRelIn : Set ((OuterStmtIn × (∀ i, OuterOStmtIn i)) × OuterWitIn))
    (innerRelIn : Set ((InnerStmtIn × (∀ i, InnerOStmtIn i)) × InnerWitIn))
    (outerRelOut : Set ((OuterStmtOut × (∀ i, OuterOStmtOut i)) × OuterWitOut))
    (innerRelOut : Set ((InnerStmtOut × (∀ i, InnerOStmtOut i)) × InnerWitOut))
    (compat : (OuterStmtIn × (∀ i, OuterOStmtIn i)) × OuterWitIn →
              (InnerStmtOut × (∀ i, InnerOStmtOut i)) × InnerWitOut → Prop)
    (lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                    OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                                    OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :=
  Context.Lens.IsComplete outerRelIn innerRelIn outerRelOut innerRelOut compat lens.toContext

/-- Conditions for the lens / transformation to preserve soundness -/
class Statement.Lens.IsSound {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    (outerLangIn : Set OuterStmtIn) (outerLangOut : Set OuterStmtOut)
    (innerLangIn : Set InnerStmtIn) (innerLangOut : Set InnerStmtOut)
    (compatStmt : OuterStmtIn → InnerStmtOut → Prop)
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut) where

  proj_sound : ∀ outerStmtIn,
    outerStmtIn ∉ outerLangIn → lens.proj outerStmtIn ∉ innerLangIn

  lift_sound : ∀ outerStmtIn innerStmtOut,
    compatStmt outerStmtIn innerStmtOut →
    innerStmtOut ∉ innerLangOut →
    lens.lift outerStmtIn innerStmtOut ∉ outerLangOut

/-- The soundness condition for the oracle statement lens is just the one for the underlying
  statement lens -/
@[reducible, simp]
def OracleStatement.Lens.IsSound {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
    (outerLangIn : Set (OuterStmtIn × (∀ i, OuterOStmtIn i)))
    (outerLangOut : Set (OuterStmtOut × (∀ i, OuterOStmtOut i)))
    (innerLangIn : Set (InnerStmtIn × (∀ i, InnerOStmtIn i)))
    (innerLangOut : Set (InnerStmtOut × (∀ i, InnerOStmtOut i)))
    (compatStmt :
      OuterStmtIn × (∀ i, OuterOStmtIn i) → InnerStmtOut × (∀ i, InnerOStmtOut i) → Prop)
    (lens : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                    OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut) :=
  Statement.Lens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut compatStmt lens

/-- Conditions for the extractor lens to preserve knowledge soundness -/
class Extractor.Lens.IsKnowledgeSound
    {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (outerRelIn : Set (OuterStmtIn × OuterWitIn))
    (innerRelIn : Set (InnerStmtIn × InnerWitIn))
    (outerRelOut : Set (OuterStmtOut × OuterWitOut))
    (innerRelOut : Set (InnerStmtOut × InnerWitOut))
    (compatStmt : OuterStmtIn → InnerStmtOut → Prop)
    (compatWit : OuterWitOut → InnerWitIn → Prop)
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                            OuterWitIn OuterWitOut InnerWitIn InnerWitOut) where

  /-- outer_to_inner for output witness (note: for statements, it's `lift` in this condition) -/
  proj_knowledgeSound : ∀ outerStmtIn innerStmtOut outerWitOut,
    compatStmt outerStmtIn innerStmtOut →
    (lens.stmt.lift outerStmtIn innerStmtOut, outerWitOut) ∈ outerRelOut →
    (innerStmtOut, lens.wit.proj (outerStmtIn, outerWitOut)) ∈ innerRelOut

  /-- inner_to_outer for input witness (note: for statements, it's `proj` in this condition) -/
  lift_knowledgeSound : ∀ outerStmtIn outerWitOut innerWitIn,
    compatWit outerWitOut innerWitIn →
    (lens.stmt.proj outerStmtIn, innerWitIn) ∈ innerRelIn →
    (outerStmtIn, lens.wit.lift (outerStmtIn, outerWitOut) innerWitIn) ∈ outerRelIn

namespace Extractor.Lens.IsKnowledgeSound

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    {outerRelIn : Set (OuterStmtIn × OuterWitIn)}
    {innerRelIn : Set (InnerStmtIn × InnerWitIn)}
    {outerRelOut : Set (OuterStmtOut × OuterWitOut)}
    {innerRelOut : Set (InnerStmtOut × InnerWitOut)}
    (compatStmt : OuterStmtIn → InnerStmtOut → Prop)
    (compatWit : OuterWitOut → InnerWitIn → Prop)
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                OuterWitIn OuterWitOut InnerWitIn InnerWitOut)

/-- If an extractor lens is knowledge sound, then the associated statement lens is sound. -/
instance [Inhabited OuterWitOut]
    [instKS : lens.IsKnowledgeSound
                outerRelIn innerRelIn
                outerRelOut innerRelOut
                compatStmt (fun _ _ => True)] :
    lens.stmt.IsSound
      outerRelIn.language outerRelOut.language
      innerRelIn.language innerRelOut.language
      compatStmt := sorry

end Extractor.Lens.IsKnowledgeSound

section SpecialCases

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
  {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
  {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
  {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
  {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
  {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}

namespace Statement.Lens

/-- The identity lens for the statement, which acts as identity on the input and output. -/
@[inline, reducible]
protected def id :
    Statement.Lens OuterStmtIn OuterStmtOut OuterStmtIn OuterStmtOut :=
  PFunctor.Lens.id _

alias trivial := Statement.Lens.id

end Statement.Lens

namespace OracleStatement.Lens

/-- The identity lens for the statement, which acts as identity on the input and output. -/
@[inline, reducible]
protected def id :
    OracleStatement.Lens OuterStmtIn OuterStmtOut OuterStmtIn OuterStmtOut
                        OuterOStmtIn OuterOStmtOut OuterOStmtIn OuterOStmtOut :=
  PFunctor.Lens.id _

alias trivial := OracleStatement.Lens.id

end OracleStatement.Lens

namespace Witness.Lens

/-- The identity lens for the witness, which acts as projection from the context (statement +
  witness) to the witness. -/
@[inline, reducible]
protected def id :
    Witness.Lens OuterStmtIn OuterStmtOut OuterWitIn OuterWitOut OuterWitIn OuterWitOut :=
  ⟨Prod.snd, fun _ => Prod.snd⟩

alias trivial := Witness.Lens.id

end Witness.Lens

namespace Witness.InvLens

/-- The identity inverse lens for the witness, whose projection is product projection to the second
  component, and lifting is identity. -/
@[inline, reducible]
protected def id :
    Witness.InvLens OuterStmtIn OuterWitIn OuterWitOut OuterWitIn OuterWitOut :=
  ⟨Prod.snd, fun _ => id⟩

alias trivial := Witness.InvLens.id

end Witness.InvLens

namespace Context.Lens

/-- The identity lens for the context, which combines the identity statement and witness lenses. -/
@[inline, reducible]
protected def id :
    Context.Lens OuterStmtIn OuterStmtOut OuterStmtIn OuterStmtOut
                OuterWitIn OuterWitOut OuterWitIn OuterWitOut where
  stmt := Statement.Lens.id
  wit := Witness.Lens.id

alias trivial := Context.Lens.id

end Context.Lens

namespace OracleContext.Lens

/-- The identity lens for the context, which combines the identity statement and witness lenses. -/
@[inline, reducible]
protected def id :
    OracleContext.Lens OuterStmtIn OuterStmtOut OuterStmtIn OuterStmtOut
                OuterOStmtIn OuterOStmtOut OuterOStmtIn OuterOStmtOut
                OuterWitIn OuterWitOut OuterWitIn OuterWitOut where
  stmt := OracleStatement.Lens.id
  wit := Witness.Lens.id

alias trivial := OracleContext.Lens.id

end OracleContext.Lens

namespace Extractor.Lens

end Extractor.Lens

end SpecialCases
