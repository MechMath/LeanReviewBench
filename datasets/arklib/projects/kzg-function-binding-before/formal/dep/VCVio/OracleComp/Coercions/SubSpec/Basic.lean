module

public import Batteries.Control.AlternativeMonad
public import Batteries.Control.OptionT
public import Batteries.Tactic.Lint
public import Batteries.Tactic.Lint.Basic
public import Cslib.Foundations.Control.Monad.IsMonadHom
public import Cslib.Foundations.Control.Monad.IsMonadHom.List
public import Cslib.Foundations.Data.PFunctor.Free
public import Cslib.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Control.Basic
public import Mathlib.Control.Monad.Basic
public import Mathlib.Control.Monad.Writer
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.FinEnum
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Functor
public import Mathlib.Data.Vector.Basic
public import Mathlib.Data.Vector.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Util.Notation3
public import Std.Internal.ForIn
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
public import dep.ToMathlib.Data.Vector.Induction
public import dep.VCVio.EvalDist.Defs.Support
public import dep.VCVio.OracleComp.HasQuery.Basic
public import dep.VCVio.OracleComp.OracleComp
public import dep.VCVio.OracleComp.OracleQuery
public import dep.VCVio.OracleComp.OracleSpec
public import dep.VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import dep.VCVio.OracleComp.SimSemantics.SimulateQ
public import dep.VCVio.OracleComp.Support
public import dep.dep.CslibCompat.Basic
public import dep.dep.CslibCompat.Free

public section

open OracleSpec OracleComp ENNReal

universe u u' v v' w w'

open scoped OracleSpec.PrimitiveQuery

variable {ι : Type u} {τ : Type v}
  {spec : OracleSpec ι} {superSpec : OracleSpec τ} {α β γ : Type w}

namespace OracleSpec

/-- Inclusion of one set of oracles into another, packaged as a polynomial-functor
lens between the underlying `OracleSpec`s. Carries the forward translation
`onQuery` on query inputs and the fiberwise backward translation `onResponse`
on query responses, plus the resulting `MonadLift` action.

The `MonadLift` action and the lens data are related by the public coherence equation
`liftM_eq_lift`. Concrete inclusions supply their query action alongside the query and response
translations. `SubSpec.liftQuery` and `SubSpec.toLens` expose those constructions independently of
any measure interpretation.

Informally, `spec ⊂ₒ superSpec` says that any query to an oracle of `spec`
can be perfectly simulated by a query to an oracle of `superSpec`. We avoid
the built-in `Subset` notation because we care about the actual data of the
mapping (it is needed when defining type coercions), not just its existence. -/
class SubSpec (spec : OracleSpec.{u, w} ι) (superSpec : OracleSpec.{v, w} τ)
    extends MonadLift (OracleQuery spec) (OracleQuery superSpec) where
  /-- Forward translation on query inputs (oracle indices). -/
  onQuery : spec.Domain → superSpec.Domain
  /-- Fiberwise backward translation on query responses. -/
  onResponse : (t : spec.Domain) → superSpec.Range (onQuery t) → spec.Range t
  /-- Coherence between the `MonadLift` action and the lens data: lifting a
  query is the lens applied to that query. Concrete instances supply
  `monadLift` directly in the lens form, making this `rfl`. -/
  liftM_eq_lift : ∀ {β : Type w} (q : OracleQuery spec β),
      monadLift q = ⟨onQuery q.input, q.cont ∘ onResponse q.input⟩ := by
    intros; rfl

@[inherit_doc] infix : 50 " ⊂ₒ " => SubSpec

namespace SubSpec

variable {κ : Type w'} {spec₃ : OracleSpec κ}

/-- The polynomial-functor lens between the underlying `PFunctor`s carried by
a `SubSpec` instance. This is the lens-level view of the data; concrete
properties (like cartesianness via `LawfulSubSpec`) are stated on this lens.

The other half of the data, `monadLift`, is fixed by `liftM_eq_lift` to be
the standard action of this lens on `OracleQuery`. -/
@[expose]
def toLens (h : SubSpec spec superSpec) :
    PFunctor.Lens spec.toPFunctor superSpec.toPFunctor where
  toFunA := h.onQuery
  toFunB := h.onResponse

/-- Transitivity of `SubSpec`: lens composition. -/
@[expose, reducible] def trans (h₁ : spec ⊂ₒ superSpec) (h₂ : superSpec ⊂ₒ spec₃) :
    spec ⊂ₒ spec₃ where
  monadLift q :=
    ⟨h₂.onQuery (h₁.onQuery q.input),
      q.cont ∘ h₁.onResponse q.input ∘ h₂.onResponse (h₁.onQuery q.input)⟩
  onQuery t := h₂.onQuery (h₁.onQuery t)
  onResponse t r := h₁.onResponse t (h₂.onResponse (h₁.onQuery t) r)

end SubSpec

/-- `LawfulSubSpec` extends `SubSpec` with the requirement that the backward
translation `onResponse` is bijective on every fiber. Equivalently: the
underlying lens `SubSpec.toLens` is *cartesian* in the sense of
`PFunctor.Lens.IsCartesian`, i.e. it is a fiberwise isomorphism over an
arbitrary forward map on positions.

This is *strictly weaker* than `PFunctor.Lens.Equiv`, which would also force
`onQuery` to be a bijection. We intentionally only require fiberwise
bijectivity because the canonical `SubSpec` instances embed a small spec
into a larger one (e.g. `spec₁ ⊂ₒ (spec₁ + spec₂)` with `onQuery = Sum.inl`),
and these embeddings are essential to the API.

Cartesianness preserves operational possibilities and permits transport of uniform measures.
Preservation of arbitrary weighted measures is a separate semantic contract. The public
`LawfulSubSpec.toLens_isCartesian` equation exposes the polynomial lens certificate. -/
class LawfulSubSpec (spec : OracleSpec.{u, w} ι) (superSpec : OracleSpec.{v, w} τ)
    [h : SubSpec spec superSpec] : Prop where
  /-- The backward translation is bijective on every fiber. -/
  onResponse_bijective (t : spec.Domain) :
    Function.Bijective (h.onResponse t)

/-- Lawful oracle-spec inclusion: a `SubSpec` whose response translation is
bijective on every fiber. -/
macro:50 lhs:term " ˡ⊂ₒ " rhs:term : term => `(LawfulSubSpec $lhs $rhs)

namespace LawfulSubSpec

variable {ι : Type u} {τ : Type v} {spec : OracleSpec ι} {superSpec : OracleSpec τ}
    [h : spec ⊂ₒ superSpec] [spec ˡ⊂ₒ superSpec]

end LawfulSubSpec

/-- Two oracle-spec inclusions into the same ambient spec have disjoint query
images.

Lawfulness concerns bijective response translations, while disjointness says the two lifted
query namespaces do not overlap inside the ambient interface. -/
class DisjointSubSpec
    {ι₁ : Type u} {ι₂ : Type v} {τ : Type w'}
    (spec₁ : OracleSpec.{u, w} ι₁) (spec₂ : OracleSpec.{v, w} ι₂)
    (superSpec : OracleSpec.{w', w} τ)
    [h₁ : SubSpec spec₁ superSpec] [h₂ : SubSpec spec₂ superSpec] : Prop where
  /-- The two forward query maps have disjoint images. -/
  disjoint_onQuery (t₁ : spec₁.Domain) (t₂ : spec₂.Domain) :
    h₁.onQuery t₁ ≠ h₂.onQuery t₂

/-- Oracle-spec inclusions with disjoint query images in an ambient interface. -/
macro:50 lhs:term " ⊥ₒ[" ambient:term "] " rhs:term : term =>
  `(DisjointSubSpec $lhs $rhs $ambient)

end OracleSpec

namespace OracleComp

section liftComp

/-- Lift a computation from `spec` to `superSpec` using a `SubSpec` instance on queries.
Usually `liftM` should be preferred but this can allow more explicit annotation. -/
@[expose]
def liftComp (mx : OracleComp spec α) (superSpec : OracleSpec τ)
    [h : MonadLiftT (OracleQuery spec) (OracleQuery superSpec)] :
    OracleComp superSpec α :=
    simulateQ (fun t => liftM (spec.query t)) mx

variable (superSpec : OracleSpec τ)
    [h : MonadLiftT (OracleQuery spec) (OracleQuery superSpec)]

end liftComp

section liftComp_support

variable {ι : Type u} {τ : Type v}
  {spec : OracleSpec ι} {superSpec : OracleSpec τ} {α : Type w}
  [h : spec ⊂ₒ superSpec] [spec ˡ⊂ₒ superSpec]

end liftComp_support

/-- Extend a lifting on `OracleQuery` to a lifting on `OracleComp`.

Registered as a low-priority `MonadLift` (not `MonadLiftT`) so that:

* For `spec = superSpec`, Lean's built-in `MonadLiftT.refl` (which is
  definitionally `id`) wins typeclass resolution. This is what
  `Std.WP.Spec.UnfoldLift.monadLift_refl` (a `rfl`-based lemma) needs in
  order to peel off spurious self-lifts inside terms `vcgen` walks.

* For `MonadLiftT (OracleQuery spec) (OracleComp superSpec)`, the built-in
  high-priority `MonadLift (OracleQuery superSpec) (OracleComp superSpec)` is
  tried first by `monadLiftTrans` and succeeds via the `SubSpec` chain on
  `OracleQuery`, never reaching this instance. Single-query lifts therefore
  go through the standard "lift query then embed" path with no spurious
  walk through `liftComp`.

* For `MonadLiftT (OracleComp spec) (OracleComp superSpec)` with
  `spec ≠ superSpec`, the high-priority built-in fails (no
  `MonadLiftT (OracleComp _) (OracleQuery _)`), Lean backtracks to this
  low-priority instance, and the recursive subgoal collapses via
  `MonadLiftT.refl`. The result is a single `liftComp mx superSpec`. -/
instance (priority := low) [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    MonadLift (OracleComp spec) (OracleComp superSpec) where
  monadLift mx := liftComp mx superSpec

instance [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    LawfulMonadLift (OracleComp spec) (OracleComp superSpec) := sorry

section OptionT

instance [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    MonadLift (OptionT (OracleComp spec)) (OptionT (OracleComp superSpec)) where
  monadLift mx := OptionT.mk (simulateQ (fun t => liftM (query t)) (OptionT.run mx))

instance [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    LawfulMonadLift (OptionT (OracleComp spec)) (OptionT (OracleComp superSpec)) := sorry

end OptionT

section StateT

instance {σ : Type _} [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    MonadLift (StateT σ (OracleComp spec)) (StateT σ (OracleComp superSpec)) where
  monadLift mx := StateT.mk fun s => liftComp (StateT.run mx s) superSpec

end StateT

end OracleComp
