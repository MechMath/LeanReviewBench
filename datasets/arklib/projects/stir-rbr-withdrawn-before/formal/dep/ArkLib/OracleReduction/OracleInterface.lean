module

public import Batteries.Control.AlternativeMonad
public import Batteries.Control.OptionT
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
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Control.Basic
public import Mathlib.Control.Monad.Basic
public import Mathlib.Control.Monad.Writer
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.FinEnum
public import Mathlib.Data.Finset.Basic
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
public import Mathlib.Probability.UniformOn
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Attr.Register
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.EMetricSpace.Weak
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Util.Notation3
public import Std.Internal.ForIn
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
public import dep.ToMathlib.MeasureTheory.MeasurableSpace.Option
public import dep.ToMathlib.MeasureTheory.Measure.Option
public import dep.ToMathlib.MeasureTheory.Measure.Subprobability
public import dep.VCVio.EvalDist.Defs.Measure.Core
public import dep.VCVio.EvalDist.Defs.Measure.Failure
public import dep.VCVio.EvalDist.Defs.Measure.OptionT
public import dep.VCVio.EvalDist.Defs.Support
public import dep.VCVio.EvalDist.Defs.Support.Failure
public import dep.VCVio.EvalDist.EvalDistEq
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

universe u v w

open OracleComp OracleSpec OracleQuery

/-- `OracleInterface` is a type class that provides an oracle interface for a type `Message`.
  It consists of:
  - a query type `Query`,
  - a response type `Response`,
  - a function `answer` that given a message `m : Message` and a query `q : Query`,
  returns a response `r : Response`.

TODO: turn `(Query, Response)` into a general `PFunctor` (i.e. `Response : Query → Type`) This
allows for better compositionality of `OracleInterface`, including (indexed) sum, instead of
requiring indexed family of `OracleInterface`s.

However, this won't be possible until `OracleSpec` is changed to be an alias for `PFunctor`

dtumad: Eventually I think we should directly use `OracleContext` instead? -/
@[ext]
class OracleInterface (Message : Type u) where
  Query : Type v
  toOC : OracleContext Query (ReaderM Message)

def OracleContext.ofFunction (α β : Type _) :
    OracleContext α (ReaderM (α → β)) where
  spec := α →ₒ β
  impl q := do return (← read) q

namespace OracleInterface

def Response {Message : Type*} [O : OracleInterface Message]
    (q : O.Query) : Type _ :=
  O.toOC.spec q

def spec {Message : Type*} [O : OracleInterface Message] :
    OracleSpec O.Query :=
  O.toOC.spec

@[implicit_reducible]
def answer {Message : Type*} [O : OracleInterface Message]
    (m : Message) (q : O.Query) : O.Response q :=
  (O.toOC.impl q).run m

/-- Pointwise decidable response equality induces a decidable predicate for equality of two
oracle answers. Keeping this at the `answer` API boundary avoids exposing its `ReaderM`
implementation merely to construct a finite filter. -/
instance instDecidablePredAnswerEq {Message : Type*} [O : OracleInterface Message]
    [∀ q, DecidableEq (O.toOC.spec q)] (a b : Message) :
    DecidablePred (fun q => answer a q = answer b q) := fun q =>
  (inferInstance : DecidableEq (O.toOC.spec q)) (answer a q) (answer b q)

/-- The default instance for `OracleInterface`, where the query is trivial (a `Unit`) and the
  response returns the data. We do not register this as an instance, instead explicitly calling it
  where necessary.
-/
@[reducible]
def instDefault {Message : Type u} : OracleInterface Message where
  Query := Unit
  toOC.spec := fun _ => Message
  toOC.impl _ := read

instance {Message : Type*} : Inhabited (OracleInterface Message) :=
  ⟨instDefault⟩

/-- Converts an indexed type family of oracle interfaces into an oracle specification.

Notation: `[v]ₒ` for when the oracle interfaces can be inferred, and `[v]ₒ'O` for when the oracle
interfaces need to be specified. -/
def toOracleSpec {ι : Type u} (v : ι → Type v) [O : ∀ i, OracleInterface (v i)] :
    OracleSpec ((i : ι) × (O i).Query) := fun q => (O q.1).Response q.2

@[inherit_doc] notation "[" v "]ₒ" => toOracleSpec v

@[inherit_doc] notation "[" v "]ₒ'" oI:max => toOracleSpec v (O := oI)

/-- Any function type has a canonical `OracleInterface` instance, whose `answer` is the function
  itself. -/
instance (i : Fin 0) : OracleInterface i.elim0 := Fin.elim0 i

@[reducible, inline]
instance instFunction {α β : Type _} : OracleInterface (α → β) where
  Query := α
  toOC := OracleContext.ofFunction α β

@[reducible, inline]
instance {ι₁ : Type u} {T₁ : ι₁ → Type v} [inst₁ : ∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type u} {T₂ : ι₂ → Type v} [inst₂ : ∀ i, OracleInterface (T₂ i)] :
    ∀ i, OracleInterface (Sum.rec T₁ T₂ i) :=
  fun i => match i with
    | .inl i => inst₁ i
    | .inr i => inst₂ i

/-- The tensor product oracle interface for the product of two types `α` and `β`, each with its own
  oracle interface, is defined as:
  - The query & response types are the product of the two query & response types.
  - The oracle will run both oracles and return the pair of responses.

This is a low priority instance since we do not expect to have this behavior often. See `instProd`
for the sum behavior on the interface. -/
@[reducible, inline]
instance (priority := low) instTensorProd {α β : Type*}
    [Oα : OracleInterface α] [Oβ : OracleInterface β] : OracleInterface (α × β) where
  Query := Oα.Query × Oβ.Query
  toOC.spec := fun | (q₁, q₂) => Oα.Response q₁ × Oβ.Response q₂
  toOC.impl := fun | (q₁, q₂) => do
    let (a, b) ← read
    return (Oα.answer a q₁, Oβ.answer b q₂)

/-- The product oracle interface for the product of two types `α` and `β`, each with its own oracle
  interface, is defined as:
  - The query & response types are the sum type of the two query & response types.
  - The oracle will answer depending on the input query.

This is the behavior more often assumed, i.e. when we send multiple oracle messages in a round.
See `instTensor` for the tensor product behavior on the interface. -/
@[reducible, inline]
instance instProd {α β : Type} [Oα : OracleInterface α] [Oβ : OracleInterface β] :
    OracleInterface (α × β) where
  Query := Oα.Query ⊕ Oβ.Query
  toOC.spec := Sum.elim Oα.spec Oβ.spec
  toOC.impl := QueryImpl.addReaderT Oα.toOC.impl Oβ.toOC.impl

/-- The indexed tensor product oracle interface for the dependent product of a type family `v`,
    indexed by `ι`, each having an oracle interface, is defined as:
  - The query & response types are the dependent product of the query & response types of the type
    family.
  - The oracle, on a given query specifying the index `i` of the type family, will run the oracle of
    `v i` and return the response.

This is a low priority instance since we do not expect to have this behavior often. See
`instProdForall` for the product behavior on the interface (with dependent sums for the query and
response types). -/
@[reducible, inline]
instance (priority := low) instTensorForall {ι : Type u} (v : ι → Type _)
    [O : ∀ i, OracleInterface (v i)] : OracleInterface (∀ i, v i) where
  Query := (i : ι) × (O i).Query
  toOC.spec := fun q => (O q.1).Response q.2
  toOC.impl q := do return (O q.1).answer ((← read) q.1) q.2

/-- The indexed product oracle interface for the dependent product of a type family `v`, indexed by
    `ι`, each having an oracle interface, is defined as:
  - The query & response types are the dependent product of the query & response types of the type
    family.
  - The oracle, on a given query specifying the index `i` of the type family, will run the oracle
    of `v i` and return the response.

This is the behavior usually assumed, i.e. when we send multiple oracle messages in a round.
See `instTensorForall` for the tensor product behavior on the interface. -/
@[reducible, inline]
instance instProdForall {ι : Type u} (v : ι → Type _) [O : ∀ i, OracleInterface (v i)] :
    OracleInterface (∀ i, v i) where
  Query := (i : ι) × (O i).Query
  toOC.spec := fun q => (O q.1).Response q.2
  toOC.impl q := do return (O q.1).answer ((← read) q.1) q.2

/-- Auto apply the `ReaderM` monad in the underlying `QueryImpl` to get an `Id` final monad. -/
def simOracle0 {ι : Type _} (T : ι → Type _)
    [O : ∀ i, OracleInterface (T i)]
    (t : (i : ι) → T i) : QueryImpl [T]ₒ Id :=
  fun q => (O q.1).answer (t q.1) q.2

/-- Combines multiple oracle specifications into a single oracle by routing queries to the
      appropriate underlying oracle. Takes:
    - A base oracle specification `oSpec`
    - Two indexed type families `T₁` and `T₂` with `OracleInterface` instances
    - Values of those type families
  Returns a stateless oracle that routes queries to the appropriate underlying oracle. -/
def simOracle2 {ι : Type u} (oSpec : OracleSpec ι)
    {ι₁ : Type v} {T₁ : ι₁ → Type w}
    [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type v} {T₂ : ι₂ → Type w}
    [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i) :
    QueryImpl (oSpec + ([T₁]ₒ + [T₂]ₒ)) (OracleComp oSpec) :=
  QueryImpl.addLift (QueryImpl.id oSpec)
    (QueryImpl.add (simOracle0 T₁ t₁) (simOracle0 T₂ t₂))

section Polynomial

open Polynomial MvPolynomial

variable (R : Type _) [CommSemiring R] (d : ℕ) (σ : Type*)

/-- Univariate polynomials can be accessed via evaluation queries. -/
@[reducible, inline]
instance instPolynomial : OracleInterface R[X] where
  Query := R
  toOC.spec := R →ₒ R
  toOC.impl point := do return (← read).eval point

/-- Univariate polynomials with degree at most `d` can be accessed via evaluation queries. -/
@[reducible, inline]
instance instPolynomialDegreeLE : OracleInterface (R⦃≤ d⦄[X]) where
  Query := R
  toOC.spec := R →ₒ R
  toOC.impl point := do return (← read).1.eval point

/-- Univariate polynomials with degree less than `d` can be accessed via evaluation queries. -/
@[reducible, inline]
instance instPolynomialDegreeLT : OracleInterface (R⦃< d⦄[X]) where
  Query := R
  toOC.spec := R →ₒ R
  toOC.impl point := do return (← read).1.eval point

/-- Multivariate polynomials can be accessed via evaluation queries. -/
noncomputable instance instMvPolynomial : OracleInterface (R[X σ]) where
  Query := (σ → R)
  toOC.spec := (σ → R) →ₒ R
  toOC.impl points := do return (← read).eval points

/-- Multivariate polynomials with individual degree at most `d` can be accessed via evaluation
queries. -/
noncomputable instance instMvPolynomialDegreeLE : OracleInterface (R⦃≤ d⦄[X σ]) where
  Query := (σ → R)
  toOC.spec := (σ → R) →ₒ R
  toOC.impl points := do return (← read).1.eval points

instance [Fintype σ] [DecidableEq σ] [Fintype R] :
    Fintype (OracleInterface.Query (R⦃≤ d⦄[X σ])) :=
  inferInstanceAs (Fintype (σ → R))

end Polynomial

section Vector

variable {n : ℕ} {α : Type*}

/-- Vectors of the form `List.Vector α n` can be accessed via queries on their indices. -/
instance instListVector : OracleInterface (List.Vector α n) where
  Query := (Fin n)
  toOC.spec := Fin n →ₒ α
  toOC.impl i := do return (← read)[i]

/-- Vectors of the form `Vector α n` can be accessed via queries on their indices. -/
instance instVector : OracleInterface (Vector α n) where
  Query := (Fin n)
  toOC.spec := Fin n →ₒ α
  toOC.impl i := do return (← read)[i]

end Vector

end OracleInterface

section PolynomialDistance

open Polynomial MvPolynomial OracleInterface

variable {R : Type*} [CommRing R] {d : ℕ} [Fintype R] [DecidableEq R] [IsDomain R]

end PolynomialDistance
