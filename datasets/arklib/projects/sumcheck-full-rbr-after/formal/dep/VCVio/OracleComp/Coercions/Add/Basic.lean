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
public import dep.ToMathlib.Control.OptionT
public import dep.ToMathlib.Data.Vector.Induction
public import dep.VCVio.EvalDist.Defs.Support
public import dep.VCVio.OracleComp.Coercions.SubSpec.Basic
public import dep.VCVio.OracleComp.HasQuery.Basic
public import dep.VCVio.OracleComp.OracleComp
public import dep.VCVio.OracleComp.OracleQuery
public import dep.VCVio.OracleComp.OracleSpec
public import dep.VCVio.OracleComp.ProbComp.Basic
public import dep.VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import dep.VCVio.OracleComp.SimSemantics.SimulateQ
public import dep.VCVio.OracleComp.Support
public import dep.dep.CslibCompat.Basic
public import dep.dep.CslibCompat.Free

public section

open OracleSpec

open scoped OracleSpec.PrimitiveQuery

namespace OracleQuery

universe u v w

variable {ι₁} {ι₂} {ι₃} {ι₄}
  {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  {spec₃ : OracleSpec ι₃} {spec₄ : OracleSpec ι₄} {α β γ : Type u}

section instances

/-- We need `Inhabited` to prevent infinite type-class searching. -/
instance (priority := low) {τ : Type u} [Inhabited τ] {spec : OracleSpec.{u, v} τ} :
    OracleSpec.emptySpec.{u,v} ⊂ₒ spec where
  monadLift q := PEmpty.elim q.input
  onQuery t := t.elim
  onResponse t := t.elim
  liftM_eq_lift q := PEmpty.elim q.input

instance (priority := low) {τ : Type u} [Inhabited τ] {spec : OracleSpec.{u, v} τ} :
    OracleSpec.emptySpec ˡ⊂ₒ spec := sorry

section add_left

/-- Add additional oracles to the right side of the existing ones. -/
instance subSpec_add_left : spec₁ ⊂ₒ (spec₁ + spec₂) where
  monadLift q := ⟨.inl q.input, q.cont⟩
  onQuery := Sum.inl
  onResponse _ := id

instance lawfulSubSpec_add_left : spec₁ ˡ⊂ₒ (spec₁ + spec₂) := sorry

end add_left

section add_right

/-- Add additional oracles to the left side of the exiting ones. -/
instance subSpec_add_right : spec₂ ⊂ₒ (spec₁ + spec₂) where
  monadLift q := ⟨.inr q.input, q.cont⟩
  onQuery := Sum.inr
  onResponse _ := id

instance lawfulSubSpec_add_right : spec₂ ˡ⊂ₒ (spec₁ + spec₂) := sorry

instance disjointSubSpec_add_left_right :
    OracleSpec.DisjointSubSpec spec₁ spec₂ (spec₁ + spec₂) := sorry

instance disjointSubSpec_add_right_left :
    OracleSpec.DisjointSubSpec spec₂ spec₁ (spec₁ + spec₂) := sorry

end add_right

section left_add_left_add

/-- Congruence on the left summand: an inclusion `spec₁ ⊂ₒ spec₃` extends to
`spec₁ + spec₂ ⊂ₒ spec₃ + spec₂`.

Low priority so that searches whose source spec is a metavariable (notably the
`MonadLiftT (OracleComp spec) (OracleComp superSpec)` chain behind whole-computation
coercions) prefer the direct embeddings `subSpec_add_left` / `subSpec_add_right`. This keeps
such coercions a single `liftComp`, definitionally, instead of a stack of lifts through an
intermediate spec. -/
instance (priority := low) subSpec_left_add_left_add_of_subSpec [h : spec₁ ⊂ₒ spec₃] :
    spec₁ + spec₂ ⊂ₒ spec₃ + spec₂ where
  monadLift
    | ⟨.inl t, f⟩ => ⟨.inl (h.onQuery t), f ∘ h.onResponse t⟩
    | ⟨.inr t, f⟩ => ⟨.inr t, f⟩
  onQuery
    | .inl t => .inl (h.onQuery t)
    | .inr t => .inr t
  onResponse
    | .inl t => h.onResponse t
    | .inr _ => id
  liftM_eq_lift q := sorry

instance lawfulSubSpec_left_add_left_add [spec₁ ⊂ₒ spec₃]
    [spec₁ ˡ⊂ₒ spec₃] :
    spec₁ + spec₂ ˡ⊂ₒ spec₃ + spec₂ := sorry

end left_add_left_add

section right_add_right_add

/-- Congruence on the right summand: an inclusion `spec₂ ⊂ₒ spec₃` extends to
`spec₁ + spec₂ ⊂ₒ spec₁ + spec₃`.

Low priority for the same reason as `subSpec_left_add_left_add_of_subSpec`: the direct
embeddings must win metavariable-headed searches so that whole-computation coercions stay a
single `liftComp`. -/
instance (priority := low) subSpec_right_add_right_add_of_subSpec [h : spec₂ ⊂ₒ spec₃] :
    spec₁ + spec₂ ⊂ₒ spec₁ + spec₃ where
  monadLift
    | ⟨.inl t, f⟩ => ⟨.inl t, f⟩
    | ⟨.inr t, f⟩ => ⟨.inr (h.onQuery t), f ∘ h.onResponse t⟩
  onQuery
    | .inl t => .inl t
    | .inr t => .inr (h.onQuery t)
  onResponse
    | .inl _ => id
    | .inr t => h.onResponse t
  liftM_eq_lift q := sorry

instance lawfulSubSpec_right_add_right_add [spec₂ ⊂ₒ spec₃]
    [spec₂ ˡ⊂ₒ spec₃] :
    spec₁ + spec₂ ˡ⊂ₒ spec₁ + spec₃ := sorry

end right_add_right_add

section add_assoc

instance subSpec_add_assoc : spec₁ + (spec₂ + spec₃) ⊂ₒ spec₁ + spec₂ + spec₃ where
  monadLift
    | ⟨.inl t, f⟩ => ⟨.inl (.inl t), f⟩
    | ⟨.inr (.inl t), f⟩ => ⟨.inl (.inr t), f⟩
    | ⟨.inr (.inr t), f⟩ => ⟨.inr t, f⟩
  onQuery
    | .inl t => .inl (.inl t)
    | .inr (.inl t) => .inl (.inr t)
    | .inr (.inr t) => .inr t
  onResponse
    | .inl _ => id
    | .inr (.inl _) => id
    | .inr (.inr _) => id
  liftM_eq_lift q := sorry

instance lawfulSubSpec_add_assoc :
    spec₁ + (spec₂ + spec₃) ˡ⊂ₒ spec₁ + spec₂ + spec₃ := sorry

end add_assoc

section sigma

variable {σ ι} (specs : σ → OracleSpec ι)

instance subSpec_sigma {σ ι} (specs : σ → OracleSpec ι) (j : σ) :
    specs j ⊂ₒ OracleSpec.sigma specs where
  monadLift q := ⟨⟨j, q.input⟩, q.cont⟩
  onQuery t := ⟨j, t⟩
  onResponse _ := id

instance lawfulSubSpec_sigma (j : σ) :
    specs j ˡ⊂ₒ OracleSpec.sigma specs := sorry

end sigma

end instances

end OracleQuery

section tests

variable (α : Type)
  {ι₁ ι₂ ι₃ ι₄ ι ι'}
  {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  {spec₃ : OracleSpec ι₃} {spec₄ : OracleSpec ι₄}
  (coeSpec : OracleSpec ι) (coeSuperSpec : OracleSpec ι')
  [_hSub : coeSpec ⊂ₒ coeSuperSpec]

end tests
