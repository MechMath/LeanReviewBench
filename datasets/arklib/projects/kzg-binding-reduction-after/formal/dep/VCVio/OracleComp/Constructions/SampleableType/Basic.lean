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
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.FunLike.IsApply
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Sym
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Functor
public import Mathlib.Data.Vector.Basic
public import Mathlib.Data.Vector.Defs
public import Mathlib.Logic.Embedding.Basic
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
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Probability.UniformOn
public import Mathlib.Tactic.Attr.Register
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.EMetricSpace.Weak
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
public import dep.PolyFun.PFunctor.Handler
public import dep.PolyFun.PFunctor.Handler.Instrumentation
public import dep.PolyFun.PFunctor.Lens.Basic
public import dep.PolyFun.PFunctor.Obj
public import dep.ToCslib.Data.PFunctor.Free.Basic
public import dep.ToMathlib.Control.OptionT
public import dep.ToMathlib.Data.FinEnum
public import dep.ToMathlib.Data.Vector.Induction
public import dep.ToMathlib.MeasureTheory.MeasurableSpace.Option
public import dep.ToMathlib.MeasureTheory.Measure.Option
public import dep.ToMathlib.MeasureTheory.Measure.Subprobability
public import dep.VCVio.EvalDist.Defs.Measure.Core
public import dep.VCVio.EvalDist.Defs.Measure.Failure
public import dep.VCVio.EvalDist.Defs.Measure.OptionT
public import dep.VCVio.EvalDist.Defs.Support
public import dep.VCVio.EvalDist.EvalDistEq
public import dep.VCVio.EvalDist.PFunctorMeasure.Core
public import dep.VCVio.EvalDist.ProbabilityNotation
public import dep.VCVio.EvalDist.ProbabilityNotation.Attr
public import dep.VCVio.OracleComp.EvalDist.AnswerMeasure
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

universe u v w

open ENNReal MeasureTheory ProbabilityTheory

/-- A canonical uniform sampler for `β`, written `$ᵗ β`: an executable program whose output
measure is uniform for every measurable structure with measurable singletons. -/
class SampleableType (β : Type) where
  /-- The canonical sampler of `β`, written `$ᵗ β`. -/
  selectElem : ProbComp β
  /-- The canonical sampler denotes the uniform measure on `β`. -/
  evalDist_selectElem_eq_uniform :
    ∀ [MeasurableSpace β] [MeasurableSingletonClass β],
      𝒟[selectElem] = uniformOn Set.univ

/-- Select uniformly from the type `β` using a type-class provided definition. -/
@[expose]
def uniformSample (β : Type) [h : SampleableType β] : ProbComp β := h.selectElem

/-- `$ᵗ β` samples uniformly from the type `β` (the `ᵗ` is for *type*); compare `$ xs`, which
samples from a collection. -/
notation:90 "$ᵗ " α:91 => uniformSample α

/-- A sampler yields an element of its type: run it on default oracle answers. Low priority so
that ordinary nonemptiness instances answer first. -/
instance (priority := 100) SampleableType.nonempty (β : Type) [SampleableType β] :
    Nonempty β := sorry

/-- A uniform sampler denotes a probability measure only on a finite type. Low priority so
that ordinary finiteness instances answer first. -/
instance (priority := 100) SampleableType.finite (β : Type) [SampleableType β] : Finite β := sorry

variable (α : Type) [SampleableType α]

section instances

/-- The uniform sampler of `Fin (n + 1)`. -/
@[expose, reducible] def SampleableType.Fin (n : ℕ) : SampleableType (Fin (n + 1)) where
  selectElem := $[0..n]
  evalDist_selectElem_eq_uniform := sorry

instance (n : ℕ) [hn : NeZero n] : SampleableType (Fin n) :=
  match n, hn with
  | _ + 1, _ => SampleableType.Fin _

instance (α : Type) [Unique α] : SampleableType α where
  selectElem := return default
  evalDist_selectElem_eq_uniform := sorry

/-- A sum of oracle specs with sampleable ranges again has sampleable ranges. -/
instance {ι ι'} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    [h : ∀ t, SampleableType (spec.Range t)] [h' : ∀ t, SampleableType (spec'.Range t)] :
    ∀ t, SampleableType ((spec + spec').Range t)
  | .inl t => h t
  | .inr t => h' t

/-- Select a uniform element from `α × β` by independently selecting from `α` and `β`. -/
instance (α β : Type) [SampleableType α] [SampleableType β] : SampleableType (α × β) where
  selectElem := (·, ·) <$> ($ᵗ α) <*> ($ᵗ β)
  evalDist_selectElem_eq_uniform := sorry

/-- Transport a uniform sampler along an equivalence. -/
@[expose, reducible] def SampleableType.ofEquiv {α β : Type} [SampleableType α] (e : α ≃ β) :
    SampleableType β where
  selectElem := e <$> ($ᵗ α)
  evalDist_selectElem_eq_uniform := sorry

/-- Any finitely enumerable type can be sampled uniformly using the underlying equivalence. -/
instance FinEnum.SampleableType (α : Type) [h : FinEnum α] [Nonempty α] : SampleableType α :=
  haveI : NeZero (FinEnum.card α) := NeZero.mk FinEnum.card_ne_zero
  SampleableType.ofEquiv h.equiv.symm

instance (n : ℕ) [NeZero n] : FinEnum (ZMod n) where
  card := n
  equiv := (ZMod.finEquiv n).symm.toEquiv

instance : FinEnum USize where
  card := 2 ^ System.Platform.numBits
  equiv := ⟨USize.toFin, USize.ofFin, fun x => sorry, fun x => sorry⟩

instance : FinEnum ISize where
  card := 2 ^ System.Platform.numBits
  equiv := ⟨BitVec.toFin ∘ ISize.toBitVec, ISize.ofBitVec ∘ BitVec.ofFin,
    fun x => sorry, fun x => sorry⟩

/-- The array-backed `Vector α n` is equivalent to an `n`-indexed function. -/
@[expose]
def arrayVectorEquivFin (α : Type u) (n : ℕ) : Vector α n ≃ (Fin n → α) where
  toFun v i := v[i.1]
  invFun := Vector.ofFn
  left_inv v := sorry
  right_inv f := funext fun i => sorry

/-- `Vector α n` is finite when `α` is finite, via the equivalence with `Fin n → α`. -/
instance instFintypeVector (α : Type u) (n : ℕ) [Fintype α] : Fintype (Vector α n) :=
  Fintype.ofEquiv (Fin n → α) (arrayVectorEquivFin α n).symm

/-- Finite entries give a finite array-backed vector type. -/
instance instFiniteVector (α : Type u) (n : ℕ) [Finite α] : Finite (Vector α n) := sorry

/-- Sample a `Vector α n` by independently sampling `α` at each index. -/
def SampleableType.vector (α : Type) [SampleableType α] : (n : ℕ) → ProbComp (Vector α n)
  | 0 => pure #v[]
  | m + 1 => Vector.push <$> SampleableType.vector α m <*> ($ᵗ α)

/-- Independent uniform samples at each index give the uniform measure on `Vector α n`. -/
theorem SampleableType.evalDist_vector (α : Type) [SampleableType α] :
    ∀ (n : ℕ) [MeasurableSpace (Vector α n)] [MeasurableSingletonClass (Vector α n)],
      𝒟[SampleableType.vector α n] = uniformOn Set.univ := sorry

instance (α : Type) (n : ℕ) [SampleableType α] : SampleableType (Vector α n) where
  selectElem := SampleableType.vector α n
  evalDist_selectElem_eq_uniform := SampleableType.evalDist_vector α n

/-- A function from `Fin n` to a `SampleableType` is also `SampleableType`. This is the base
case used by the general `FinEnum`-indexed `instSampleableTypeFunc` below. -/
instance instSampleableTypeFinFunc {n : ℕ} {α : Type} [SampleableType α] :
    SampleableType (Fin n → α) :=
  SampleableType.ofEquiv (arrayVectorEquivFin α n)

/-- A function `β → α` for `β` finitely enumerable and `α` sampleable is itself sampleable.
This generalizes the `Fin n → α` instance above: the `FinEnum.fin` instance recovers it. -/
instance instSampleableTypeFunc {β α : Type} [FinEnum β] [SampleableType α] :
    SampleableType (β → α) :=
  SampleableType.ofEquiv (α := Fin (FinEnum.card β) → α)
    (Equiv.arrowCongr FinEnum.equiv.symm (Equiv.refl α))

/-- Select a uniform element from `List.Vector α n` by independently selecting `α` at each
index. The construction goes through the equivalence with `Fin n → α`. -/
instance instSampleableTypeListVector {α : Type} {n : ℕ} [SampleableType α] :
    SampleableType (List.Vector α n) :=
  SampleableType.ofEquiv (Equiv.vectorEquivFin α n).symm

/-- Select a uniform element from `Matrix ι κ α` by independently selecting an entry for each
`(i, j)`. Both index types only need to be `FinEnum`. -/
instance instSampleableTypeMatrix {α ι κ : Type} [FinEnum ι] [FinEnum κ] [SampleableType α] :
    SampleableType (Matrix ι κ α) :=
  inferInstanceAs (SampleableType (ι → κ → α))

/-- Discoverability wrapper: `SampleableType (α ⊕ β)` follows from `FinEnum` on each side
plus nonemptiness of the sum, via Mathlib's `FinEnum.sum` instance and
`FinEnum.SampleableType`. Listed explicitly so users can see it in the instance set rather
than relying on a multi-step search. -/
instance instSampleableTypeSum {α β : Type} [FinEnum α] [FinEnum β]
    [Nonempty (α ⊕ β)] : SampleableType (α ⊕ β) :=
  inferInstance

/-- Discoverability wrapper: `SampleableType (Finset α)` for `FinEnum α`. Uniform sampling
draws every subset of `α` with the same probability (`2^|α|` outcomes). `Finset α` is always
inhabited by `∅`, so no `Nonempty` hypothesis is needed. -/
instance instSampleableTypeFinset {α : Type} [FinEnum α] : SampleableType (Finset α) :=
  inferInstance

/-- Uniform sampling of size-`n` multisets over a `FinEnum` type. `Sym α n` is the correct finite
analogue of `Multiset α`: a plain `Multiset α` is unbounded in multiplicity and thus not finite,
while `Sym α n` is finite whenever `α` is. We obtain a *computable* uniform sampler from the
canonical enumeration `Sym.finEnum`; for a base type with only a `Fintype` instance use
`SampleableType.ofFintype` instead.

Note this is genuinely uniform on multisets: mapping a uniform `List.Vector α n` through
`Sym.ofVector` is *not* (it weights each multiset by its number of orderings), so we enumerate
`Sym α n` canonically rather than pushing forward from vectors. -/
instance instSampleableTypeSym {α : Type} {n : ℕ} [FinEnum α] [Nonempty α] :
    SampleableType (Sym α n) :=
  letI : FinEnum (Sym α n) := Sym.finEnum n
  haveI : Nonempty (Sym α n) := ⟨Sym.replicate n (Classical.arbitrary α)⟩
  FinEnum.SampleableType _

/-- Uniform sampling of permutations of a `FinEnum` type. `Equiv.Perm α` has `n!` elements when
`Fintype.card α = n`. We obtain a *computable* uniform sampler from the canonical enumeration
`Equiv.Perm.finEnum`. Useful for shuffle-based protocols and oblivious-permutation games. -/
instance instSampleableTypePerm {α : Type} [FinEnum α] :
    SampleableType (Equiv.Perm α) :=
  letI : FinEnum (Equiv.Perm α) := Equiv.Perm.finEnum
  haveI : Nonempty (Equiv.Perm α) := ⟨Equiv.refl α⟩
  FinEnum.SampleableType _

/-- Uniform sampling of injections `β ↪ α` for `FinEnum` types. The number of such embeddings is
`α.card! / (α.card - β.card)!` when `β.card ≤ α.card`, else `0`; the `Nonempty (β ↪ α)`
hypothesis rules out the latter case. We obtain a *computable* uniform sampler from the canonical
enumeration `Function.Embedding.finEnum` (itself computable, unlike Mathlib's `Fintype (β ↪ α)`). -/
instance instSampleableTypeEmbedding {β α : Type}
    [FinEnum β] [FinEnum α] [Nonempty (β ↪ α)] :
    SampleableType (β ↪ α) :=
  letI : FinEnum (β ↪ α) := Function.Embedding.finEnum
  FinEnum.SampleableType _

/-- A function from a finite type `D` with `Fintype` + `DecidableEq` (not necessarily `FinEnum`)
to a `SampleableType` is itself `SampleableType`, transporting the `Fin (Fintype.card D) → α`
sampler across the canonical equivalence `(D → α) ≃ (Fin (Fintype.card D) → α)`.

This is the *noncomputable* counterpart to the computable `FinEnum`-domain instance
`instSampleableTypeFunc`, and is given **lower priority** so that for a `FinEnum` domain the
computable instance is preferred; it is the fallback for `Fintype` + `DecidableEq`-only domains. -/
noncomputable instance (priority := 100) instSampleableTypePiFintype {D : Type}
    [Fintype D] [DecidableEq D] {α : Type} [SampleableType α] : SampleableType (D → α) :=
  -- Provide the `Fin (card D) → α` sampler explicitly: synthesizing it could loop, since for the
  -- abstract `Fintype.card D` the overlapping `instSampleableTypeFunc` descends without converging.
  letI : SampleableType (Fin (Fintype.card D) → α) := instSampleableTypeFinFunc
  SampleableType.ofEquiv
    (α := Fin (Fintype.card D) → α)
    (Equiv.arrowCongr (Fintype.equivFin D).symm (Equiv.refl α))

end instances

section UniformSampleImpl

open OracleSpec OracleComp

variable {ι : Type*} {spec : OracleSpec ι}

/-- Given that the output type of all oracles has a `SampleableType` instance, replace all queries
with uniformly random responses by calling the corresponding `uniformSample` at each query. -/
@[expose] def uniformSampleImpl [∀ i, SampleableType (spec.Range i)] :
    QueryImpl spec ProbComp := fun t => $ᵗ spec.Range t

namespace uniformSampleImpl

variable [∀ i, SampleableType (spec.Range i)]

end uniformSampleImpl

end UniformSampleImpl
