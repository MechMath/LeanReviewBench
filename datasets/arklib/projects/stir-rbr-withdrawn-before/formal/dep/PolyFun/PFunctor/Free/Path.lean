module

public import Batteries.Tactic.Lint
public import Cslib.Foundations.Data.PFunctor.Free
public import Cslib.Init
public import Mathlib.Control.Monad.Basic
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Util.Notation3
public import dep.PolyFun.Control.Monad.Hom
public import dep.PolyFun.PFunctor.Basic
public import dep.PolyFun.PFunctor.Equiv.Basic
public import dep.PolyFun.PFunctor.Free.Displayed
public import dep.PolyFun.PFunctor.Lens.Basic
public import dep.PolyFun.PFunctor.Obj
public import dep.ToCslib.Data.PFunctor.Free.Basic
public import dep.dep.CslibCompat.Basic
public import dep.dep.CslibCompat.Free

@[expose] public section

universe v w z t uA uB uA₂ uB₂

namespace PFunctor

namespace FreeM

variable {P : PFunctor.{uA, uB}} {α : Type v}

variable {Q : PFunctor.{uA₂, uB₂}}

/-- Displayed algebra for canonical root-to-leaf paths: a leaf carries the trivial fiber
`PUnit`, and a node at `a : P.A` carries the dependent sum, over directions `b : P.B a`, of the
fiber chosen for the child `b`. `Path` is its evaluation; `PathAlong.algebra` is the variant
whose node directions come from a runtime polynomial along a lens. -/
@[implicit_reducible]
def Path.algebra (P : PFunctor.{uA, uB}) (α : Type v) :
    Displayed.Algebra.{uA, uB, v, uB+1} P α where
  leaf := fun _ => PUnit.{uB+1}
  node := fun a child => (b : P.B a) × child b

/-- The canonical root-to-leaf path through a `FreeM` tree. A path through `pure x` is trivial
(`PUnit`); a path through `(FreeM.lift a).bind rest` is a direction `b : P.B a` together with a
path through `rest b`. Prefer `Path.cons`, `Path.head` and `Path.tail` for node paths: they keep
statements independent of how `Displayed` unfolds. `PathAlong l s` is the runtime variant whose
node directions come from the target polynomial of the lens `l`. -/
abbrev Path {α : Type v} : FreeM P α → Type uB :=
  Displayed (Path.algebra P α)

namespace Path

/-- Prepend one operation-node direction to a path through the selected child. -/
def cons (a : P.A) (rest : P.B a → FreeM P α) (b : P.B a) (path : Path (rest b)) :
    Path ((FreeM.lift a).bind rest) :=
  ⟨b, path⟩

/-- The direction selected at the root of a non-leaf path. -/
def head (a : P.A) (rest : P.B a → FreeM P α) (path : Path ((FreeM.lift a).bind rest)) : P.B a :=
  path.1

/-- The path remaining below the root direction of a non-leaf path. -/
def tail (a : P.A) (rest : P.B a → FreeM P α) (path : Path ((FreeM.lift a).bind rest)) :
    Path (rest (head a rest path)) :=
  path.2

/-- Two paths through a node agree once their directions and tails agree. The tail hypothesis is
heterogeneous because the tails live over the two heads; when the heads are already syntactically
equal, supply it with `heq_of_eq`. This is `Sigma.ext` seen through the node interface; it is
deliberately not an `@[ext]` lemma, since `Path` is an abbreviation of `Displayed`. -/
theorem ext {a : P.A} {rest : P.B a → FreeM P α} {path path' : Path ((FreeM.lift a).bind rest)}
    (hhead : head a rest path = head a rest path')
    (htail : HEq (tail a rest path) (tail a rest path')) : path = path' := sorry

end Path

/-- Displayed algebra for runtime paths along a lens `l : Lens P Q`: a leaf carries the trivial
fiber `PUnit`, and a node at `a : P.A` carries the dependent sum, over runtime directions
`d : Q.B (l.toFunA a)` of the target polynomial, of the fiber chosen for the source branch
`l.toFunB a d` that `d` selects. `PathAlong` is its evaluation; `Path.algebra` is the variant whose
node directions are the source directions `P.B a` themselves. -/
@[implicit_reducible]
def PathAlong.algebra (l : Lens P Q) : Displayed.Algebra.{uA, uB, v, uB₂+1} P α where
  leaf := fun _ => PUnit.{uB₂+1}
  node := fun a child => (d : Q.B (l.toFunA a)) × child (l.toFunB a d)

/-- Runtime path through a `P`-tree `s` executed along a lens `l : Lens P Q`. A path through
`pure x` is trivial (`PUnit`); a path through `(FreeM.lift a).bind rest` is a runtime direction
`d : Q.B (l.toFunA a)` together with a path through the source branch `rest (l.toFunB a d)` that `d`
selects. Prefer `PathAlong.cons`, `PathAlong.head` and `PathAlong.tail` for node paths. It is
`Path (s.mapLens l)` up to `PathAlong.toMapLensPath`; `projectPathAlong` forgets it to `Path s`. -/
abbrev PathAlong (l : Lens P Q) (s : FreeM P α) : Type uB₂ :=
  Displayed (PathAlong.algebra l) s

namespace PathAlong

/-- Prepend one runtime direction to a runtime path through the branch it selects. -/
def cons (l : Lens P Q) (a : P.A) (rest : P.B a → FreeM P α) (d : Q.B (l.toFunA a))
    (path : PathAlong l (rest (l.toFunB a d))) : PathAlong l ((FreeM.lift a).bind rest) :=
  ⟨d, path⟩

end PathAlong

/-- The leaf payload selected by a path. The path records only branch choices, but together with
the tree it determines the terminal `pure` payload. `output_pure` and `output_liftBind` are its
equations; `outputAlong` is the variant for runtime paths along a lens. -/
def output : (s : FreeM P α) → Path s → α
  | .pure x, _ => x
  | .liftBind _ rest, ⟨b, path⟩ => output (rest b) path

/-- Constructor-local projection from runtime paths along a lens `l` to control paths: a leaf
maps to the trivial path, and at a node the runtime direction `d` maps to the source direction
`l.toFunB a d` it selects. `projectPathAlong` is its `toHom` evaluation over whole trees. -/
def projectPathAlongLocalMap (l : Lens P Q) :
    Displayed.LocalMap (PathAlong.algebra (α := α) l) (Path.algebra P α) where
  mapLeaf := fun _ _ => ⟨⟩
  mapNode := fun a _ _ mapChild path => ⟨l.toFunB a path.1, mapChild (l.toFunB a path.1) path.2⟩

/-- Project a runtime path along a lens `l` back to the canonical branch path of the control tree:
at each node the runtime direction `d` becomes the source direction `l.toFunB a d` it selects.
`projectPathAlong_pure` and `projectPathAlong_liftBind` are its equations, and
`output_projectPathAlong` shows it preserves the selected payload. -/
def projectPathAlong (l : Lens P Q) : (s : FreeM P α) → PathAlong l s → Path s :=
  (projectPathAlongLocalMap l).toHom

/-- Dependent sequential composition of `FreeM` trees: `append s₁ s₂` grafts onto each leaf of `s₁`
the tree `s₂` selects for the canonical path that reached it, so a suffix may inspect the whole
branch and not merely the payload. `append_pure` and `append_liftBind` are its equations and
`append_output_eq_bind` its overlap with `>>=`. `append_assoc` makes grafting associative,
reindexing by the path pairing `Path.append` and its inverse `Path.split`. -/
@[implicit_reducible]
def append {β : Type t} : (s₁ : FreeM P α) → (Path s₁ → FreeM P β) → FreeM P β
  | .pure _, s₂ => s₂ ⟨⟩
  | .liftBind a rest, s₂ => .liftBind a fun b => append (rest b) (fun path => s₂ ⟨b, path⟩)

namespace Path

/-- Lift a two-argument family indexed by a canonical prefix path and a canonical suffix path to a
family on the appended tree, by recursion on the prefix. `liftAppend_append` cancels it against
`Path.append`, `liftAppend_split` restates it through `split`, and `packAppend`/`unpackAppend`
transport values across it. `PathAlong.LiftAppend` is the runtime form along a lens. -/
def LiftAppend {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) → ((path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    Path (FreeM.append s₁ s₂) → Type w
  | .pure _, _, F, path => F ⟨⟩ path
  | .liftBind _ rest, s₂, F, ⟨b, path⟩ =>
      LiftAppend (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂) path

@[reducible, deprecated (since := "2026-10-19")] alias liftAppend := LiftAppend

/-- Combine a canonical prefix path through `s₁` with a canonical suffix path through the tree `s₂`
grafts there, by recursion on the prefix; the leaf case is `append_pure`. `split` is the two-sided
inverse, with round trips `split_append` and `append_split`; `FreeM.append_assoc` reindexes an
iterated graft by it, and `PathAlong.append` is the runtime form along a lens. -/
def append {β : Type t} : (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) → (path₁ : Path s₁) →
    Path (s₂ path₁) → Path (FreeM.append s₁ s₂)
  | .pure _, _, _, path₂ => path₂
  | .liftBind _ rest, s₂, ⟨b, path₁⟩, path₂ =>
      ⟨b, append (rest b) (fun path => s₂ ⟨b, path⟩) path₁ path₂⟩

/-- The `pure` case of `Path.append`: a leaf prefix contributes no directions, so appending the
trivial prefix path `⟨⟩` to a suffix path returns that suffix unchanged, as `FreeM.append_pure`
does for the grafted tree. `Path.split` inverts `Path.append`, and `packAppend_pure` is the sibling
equation transporting payloads across `LiftAppend`. -/
@[simp]
theorem append_pure {β : Type t} (x : α) (s₂ : Path (FreeM.pure (P := P) x) → FreeM P β)
    (path₂ : Path (s₂ ⟨⟩)) : append (pure x) s₂ ⟨⟩ path₂ = path₂ := sorry

@[deprecated (since := "2026-10-19")] alias append_done := append_pure

/-- Associativity of path-indexed tree grafting. The suffix continuation on the right is reindexed
by `Path.append`, which pairs the outer and middle canonical paths; `Path.split` inverts it. -/
theorem _root_.PFunctor.FreeM.append_assoc {β : Type t} {γ : Type z} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) → (s₃ : Path (FreeM.append s₁ s₂) → FreeM P γ) →
      FreeM.append (FreeM.append s₁ s₂) s₃ = FreeM.append s₁ (fun path₁ =>
        FreeM.append (s₂ path₁) (fun path₂ => s₃ (Path.append s₁ s₂ path₁ path₂)))
  := sorry

@[deprecated (since := "2026-10-19")] alias append_tree_assoc := FreeM.append_assoc

/-- Transport a value of `F path₁ path₂` to the `LiftAppend` family at the appended canonical path,
following the recursion of `LiftAppend` so that no explicit equality transport is needed; the leaf
case is `packAppend_pure`. `unpackAppend` is the inverse, with `unpackAppend_packAppend` and
`packAppend_unpackAppend` the two round trips; `PathAlong.packAppend` is the runtime form
along a lens. -/
def packAppend {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) → (path₁ : Path s₁) →
    (path₂ : Path (s₂ path₁)) → F path₁ path₂ → LiftAppend s₁ s₂ F (append s₁ s₂ path₁ path₂)
  | .pure _, _, _, ⟨⟩, _, x => x
  | .liftBind _ rest, s₂, F, ⟨b, path₁⟩, path₂, x =>
      packAppend (rest b) (fun path => s₂ ⟨b, path⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂) path₁ path₂ x

/-- The `pure` case of `packAppend`: over a leaf prefix the appended path is the suffix path
itself, so the payload crosses `LiftAppend` unchanged. `append_pure` is the sibling equation and
`unpackAppend` is the inverse transport. -/
@[simp]
theorem packAppend_pure {β : Type t} (x : α) (s₂ : Path (FreeM.pure (P := P) x) → FreeM P β)
    (F : (path₁ : Path (FreeM.pure (P := P) x)) → Path (s₂ path₁) → Type w) (path₂ : Path (s₂ ⟨⟩))
    (y : F ⟨⟩ path₂) : packAppend (pure x) s₂ F ⟨⟩ path₂ y = y := sorry

@[deprecated (since := "2026-10-19")] alias packAppend_done := packAppend_pure

/-- Lift a binary relation on pair-indexed families to the fused appended path: at a leaf it is
`R` on the trivial prefix, and at a node the recursion descends under the chosen direction.
`liftAppendRel_iff` characterises it as `R` at the path pair `split` recovers, on the payloads
`unliftAppend` extracts from the two `LiftAppend` families. `LiftAppendPred` is the unary form. -/
def LiftAppendRel {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F G : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (R : ∀ (path₁ : Path s₁) (path₂ : Path (s₂ path₁)), F path₁ path₂ → G path₁ path₂ → Prop) →
    (path : Path (FreeM.append s₁ s₂)) → LiftAppend s₁ s₂ F path → LiftAppend s₁ s₂ G path → Prop
  | .pure _, _, _, _, R, path, x, y => R ⟨⟩ path x y
  | .liftBind _ rest, s₂, F, G, R, ⟨b, path⟩, x, y =>
      LiftAppendRel (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => G ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => R ⟨b, path₁⟩ path₂) path x y

@[reducible, deprecated (since := "2026-10-19")] alias liftAppendRel := LiftAppendRel

/-- Lift a unary predicate on a pair-indexed family to the fused appended path: at a leaf it is
`Pred` on the trivial prefix, and at a node the recursion descends under the chosen direction.
`liftAppendPred_iff` characterises it as `Pred` at the path pair `split` recovers, on the payload
`unliftAppend` extracts from the `LiftAppend` family. `LiftAppendRel` is the binary form. -/
def LiftAppendPred {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (Pred : ∀ (path₁ : Path s₁) (path₂ : Path (s₂ path₁)), F path₁ path₂ → Prop) →
    (path : Path (FreeM.append s₁ s₂)) → LiftAppend s₁ s₂ F path → Prop
  | .pure _, _, _, Pred, path, x => Pred ⟨⟩ path x
  | .liftBind _ rest, s₂, F, Pred, ⟨b, path⟩, x =>
      LiftAppendPred (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => Pred ⟨b, path₁⟩ path₂) path x

@[reducible, deprecated (since := "2026-10-19")] alias liftAppendPred := LiftAppendPred

end Path

namespace PathAlong

/-- Lift a two-argument family indexed by a runtime prefix path and a runtime suffix path to a
family on the appended tree, by recursion on the prefix; the suffix is selected by the control
projection of the runtime prefix. `PathAlong.liftAppend_append` cancels it against `append`,
`PathAlong.liftAppend_split` restates it through `split`, and `packAppend`, `unpackAppend` and
`unliftAppend` transport values across it. `Path.LiftAppend` is the control-path form. -/
def LiftAppend {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    ((path₁ : PathAlong l s₁) → PathAlong l (s₂ (projectPathAlong l s₁ path₁)) → Type w) →
    PathAlong l (FreeM.append s₁ s₂) → Type w
  | .pure _, _, F, path => F ⟨⟩ path
  | .liftBind a rest, s₂, F, ⟨d, path⟩ =>
      LiftAppend l (rest (l.toFunB a d)) (fun path₁ => s₂ ⟨l.toFunB a d, path₁⟩)
        (fun path₁ path₂ => F ⟨d, path₁⟩ path₂) path

@[reducible, deprecated (since := "2026-10-19")] alias liftAppend := LiftAppend

/-- Combine a runtime prefix path through `s₁` with a runtime suffix path through the tree `s₂`
grafts at the control projection `projectPathAlong l s₁ path₁` of that prefix, by recursion on the
prefix. `split` is the two-sided inverse, with round trips `split_append` and `append_split`, and
`liftAppend_append` cancels the fused family. `projectPathAlong_append` sends an appended runtime
path to `Path.append`, the control-path form whose suffix is indexed by the control path itself. -/
def append {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) → (path₁ : PathAlong l s₁) →
    PathAlong l (s₂ (projectPathAlong l s₁ path₁)) → PathAlong l (FreeM.append s₁ s₂)
  | .pure _, _, _, path₂ => path₂
  | .liftBind a rest, s₂, ⟨d, path₁⟩, path₂ =>
      ⟨d, append l (rest (l.toFunB a d)) (fun path => s₂ ⟨l.toFunB a d, path⟩) path₁ path₂⟩

attribute [local implicit_reducible] Displayed.LocalMap.toHom
  Displayed.LocalMap.toHomFun projectPathAlongLocalMap projectPathAlong

end PathAlong

/-- Indexed W-type of stopping trees for a transition system observed through an arbitrary family
`Obs`: at each state an inhabitant either stops or extends into the state `step s obs` selected by
each observation. Because `done s` is available at every state, inhabitation alone does not assert
termination. It is the initial `StoppingTree.Algebra`, with catamorphism `StoppingTree.fold` and
uniqueness lemma `StoppingTree.fold_unique`; `Telescope` specializes `Obs` to path fibres. -/
inductive StoppingTree {St : Type z} (Obs : St → Type w) (step : (s : St) → Obs s → St) :
    St → Type (max w z)
  /-- Stop at the current state, running no further transition. -/
  | done (s : St) : StoppingTree Obs step s
  /-- Run one transition layer, recursing into the state selected by each observation. -/
  | extend (s : St) (cont : (obs : Obs s) → StoppingTree Obs step (step s obs)) :
      StoppingTree Obs step s

namespace StoppingTree

variable {St : Type z} {Obs : St → Type w} {step : (s : St) → Obs s → St}

/-- Algebra for the indexed polynomial `y ↦ (fun s => PUnit ⊕ ((obs : Obs s) → y (step s obs)))`: a
`done` interpretation at each state and an `extend` interpretation of one transition layer.
`StoppingTree` is its initial algebra: `fold` is the unique homomorphism into `Carrier`, with
`fold_done` and `fold_extend` its computation rules and `fold_unique` its uniqueness. -/
structure Algebra (Carrier : St → Type t) where
  /-- Interpretation of the `StoppingTree.done` leaf at a state. -/
  done : (s : St) → Carrier s
  /-- Interpretation of a `StoppingTree.extend` layer from the value chosen by each observation. -/
  extend : (s : St) → ((obs : Obs s) → Carrier (step s obs)) → Carrier s

/-- Catamorphism out of the initial stopping-tree algebra: recursion over a `StoppingTree` that
interprets each `done` leaf and each `extend` layer by the matching field of the `Algebra` `alg`.
Its computation rules `fold_done` and `fold_extend` hold by `rfl`, and `fold_unique` is the
uniqueness half of the universal property. `Telescope.toFreeM` is `fold` at the `FreeM.append`
algebra. -/
def fold {Carrier : St → Type t} (alg : Algebra (Obs := Obs) (step := step) Carrier) :
    {s : St} → StoppingTree Obs step s → Carrier s
  | _, .done s => alg.done s
  | _, .extend s cont => alg.extend s fun obs => fold alg (cont obs)

/-- Uniqueness half of the initial-algebra universal property: any `f` satisfying the algebra
equations `hDone` and `hExtend` agrees pointwise with `fold`. `fold_done` and `fold_extend` say
that `fold alg` itself satisfies them, so it is the unique such algebra homomorphism. -/
theorem fold_unique {Carrier : St → Type t} (alg : Algebra (Obs := Obs) (step := step) Carrier)
    (f : {s : St} → StoppingTree Obs step s → Carrier s)
    (hDone : (s : St) → f (StoppingTree.done s) = alg.done s)
    (hExtend : (s : St) → (cont : (obs : Obs s) → StoppingTree Obs step (step s obs)) →
      f (StoppingTree.extend s cont) = alg.extend s (fun obs => f (cont obs))) :
    {s : St} → (tree : StoppingTree Obs step s) → f tree = fold alg tree
  := sorry

@[deprecated (since := "2026-10-19")] alias eq_fold := fold_unique

end StoppingTree

/-- `StoppingTree` with observations instantiated to the canonical path fibres `Path (round s)`:
each layer runs the round `round s` and branches on the path taken through it. `Telescope.done` and
`Telescope.extend` are the constructor wrappers, `Telescope.toFreeM` flattens a telescope into one
`FreeM` tree, and a more compact observation type should use `StoppingTree` directly. -/
abbrev Telescope {St : Type z} {Out : St → Type v} (round : (s : St) → FreeM P (Out s))
    (step : (s : St) → Path (round s) → St) : St → Type (max uB z) :=
  StoppingTree (fun s => Path (round s)) step

namespace Telescope

variable {St : Type z} {Out : St → Type v} {round : (s : St) → FreeM P (Out s)}
    {step : (s : St) → Path (round s) → St}

/-- Terminating constructor for a canonical-path telescope: `StoppingTree.done` at the observation
family `Path (round s)`, available at every state. `toFreeM_done` flattens this telescope to
`finish s`, and `Telescope.extend` runs one more round instead. -/
abbrev done (s : St) : Telescope round step s := StoppingTree.done s

/-- Extending constructor for a canonical-path telescope: `StoppingTree.extend` at the observation
family `Path (round s)`, so `cont` is indexed by the canonical branch path through the round
`round s` and resumes at the next state `step s path`. `toFreeM_extend` flattens this telescope to
an `append` of that round, and `Telescope.done` stops there instead. -/
abbrev extend (s : St) (cont : (path : Path (round s)) → Telescope round step (step s path)) :
    Telescope round step s := StoppingTree.extend s cont

end Telescope

end FreeM

end PFunctor
