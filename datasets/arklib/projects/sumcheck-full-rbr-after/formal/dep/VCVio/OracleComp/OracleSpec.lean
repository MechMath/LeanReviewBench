module

public import Cslib.Init
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Util.Notation3
public import dep.PolyFun.PFunctor.Basic
public import dep.PolyFun.PFunctor.Obj
public import dep.dep.CslibCompat.Basic

@[expose] public section

universe u u' v w

/-- An `OracleSpec ι` specifies a set of oracles indexed by `ι`.
Defined as a map from each input to the type of the oracle's output. -/
def OracleSpec (ι : Type u) : Type (max u (v + 1)) :=
  ι → Type v

attribute [implicit_reducible] OracleSpec

namespace OracleSpec

variable {ι : Type u}

@[reducible]
def toPFunctor (spec : OracleSpec ι) : PFunctor := PFunctor.mk ι spec

@[reducible, inline]
def ofPFunctor (P : PFunctor) : OracleSpec P.A := P.B

abbrev Domain (_spec : OracleSpec ι) : Type _ := ι

abbrev Range (spec : OracleSpec ι) (t : ι) : Type _ := spec t

section ofFn

@[reducible, always_inline] def ofFn {ι : Type u} (F : ι → Type v) : OracleSpec ι := F

notation:25 (name := singletonSpec) A:25 " →ₒ " B:26 =>
  OracleSpec.ofFn (ι := A) (fun _ => B)

end ofFn

section add

/-- `spec₁ + spec₂` specifies access to oracles in both `spec₁` and `spec₂`.
The input is split as a sum type of the two original input sets.
This corresponds exactly to addition of the corresponding `PFunctor`.

The ordinary instance reducibility assigned by the `instance` command lets its `HAdd.hAdd`
projection reduce while checking dependent implicit types such as
`(spec₁ + spec₂).Range (.inl t)`, without unfolding combined specifications during ordinary
reducible-transparency tactic matching. -/
instance {ι ι'} :
    HAdd (OracleSpec ι) (OracleSpec ι') (OracleSpec (ι ⊕ ι')) where
  hAdd spec spec' :=
    OracleSpec.ofPFunctor (PFunctor.add spec.toPFunctor spec'.toPFunctor)

instance {ι ι'} (spec : OracleSpec ι) (spec' : OracleSpec ι')
    [h : ∀ t, Fintype (spec.Range t)] [h' : ∀ t, Fintype (spec'.Range t)] :
    ∀ t, Fintype ((spec + spec').Range t)
  | .inl i => h i
  | .inr i => h' i

instance {ι ι'} (spec : OracleSpec ι) (spec' : OracleSpec ι')
    [h : ∀ t, DecidableEq (spec.Range t)] [h' : ∀ t, DecidableEq (spec'.Range t)] :
    ∀ t, DecidableEq ((spec + spec').Range t)
  | .inl i => h i
  | .inr i => h' i

instance {ι ι'} (spec : OracleSpec ι) (spec' : OracleSpec ι')
    [h : ∀ t, Inhabited (spec.Range t)] [h' : ∀ t, Inhabited (spec'.Range t)] :
    ∀ t, Inhabited ((spec + spec').Range t)
  | .inl i => h i
  | .inr i => h' i

end add

section sigma

/-- Given an indexed set of `OracleSpec`, specify access to all of the oracles,
by requiring an index into the corresponding oracle in the input. -/
protected def sigma {ι} {τ : ι → Type _} (specs : (i : ι) → OracleSpec (τ i)) :
    OracleSpec ((i : ι) × (specs i).Domain) :=
  fun t => specs t.1 t.2

end sigma

section mul

/-- `spec₁ * spec₂` represents an oracle that takes in a pair of inputs for each set,
and returns an element in the output of one oracle or the other.
The corresponds exactly to multiplication in `PFunctor`. -/
instance {ι ι'} : HMul (OracleSpec ι) (OracleSpec ι') (OracleSpec (ι × ι'))
  where hMul spec spec' := fun t => spec.Range t.1 ⊕ spec'.Range t.2

end mul

section pi

/-- Given an indexed set of `OracleSpec`, specify access to an oracle that given an input to
the oracle for each index returns an index and an output for that index. -/
protected def pi {ι : Type _} {τ : ι → Type _} (specs : (i : ι) → OracleSpec (τ i)) :
    OracleSpec ((i : ι) → (specs i).Domain) :=
  fun t => (i : ι) × specs i (t i)

end pi

section emptySpec

/-- Specifies access to no oracles, using the empty type as the indexing type. -/
@[reducible] def emptySpec : OracleSpec PEmpty := PEmpty →ₒ PEmpty

notation "[]ₒ" => emptySpec

end emptySpec

end OracleSpec

/-- Access to a coin flipping oracle. Because of termination rules in Lean this is slightly
weaker than `unifSpec`, as we have only finitely many coin flips. -/
@[reducible] def coinSpec : OracleSpec.{0, 0} Unit := Unit →ₒ Bool

section unifSpec

/-- Access to oracles for uniformly selecting from `Fin (n + 1)` for arbitrary `n : ℕ`.
By adding `1` to the index we avoid selection from the empty type `Fin 0 ≃ empty`. -/
@[inline, reducible] def unifSpec : OracleSpec ℕ :=
  OracleSpec.ofFn fun n => Fin (n + 1)

end unifSpec

section probSpec

/-- Select uniformly from `Fin (m + 1)` for a pair `(n, m) : ℕ × ℕ`, where the first
component is unused. -/
@[inline, reducible] def probSpec : OracleSpec (ℕ × ℕ) :=
  OracleSpec.ofFn fun (_n, m) => Fin (m + 1)

end probSpec
