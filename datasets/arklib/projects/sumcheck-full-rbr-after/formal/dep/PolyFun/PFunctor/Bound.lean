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
public import dep.PolyFun.PFunctor.Lens.Basic
public import dep.PolyFun.PFunctor.Obj
public import dep.dep.CslibCompat.Basic
public import dep.dep.CslibCompat.Free

@[expose] public section

universe v w uA uB uA₂ uB₂

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {α β : Type v} {B : Type*}

/-- Generalized roll bound on `FreeM P` parameterized by a budget type `B`,
a validity check `canRoll`, and a cost function `cost`. `pure` satisfies any
bound; `roll a r` satisfies the bound when `canRoll a b` holds and every
continuation satisfies the bound at `cost a b`. -/
def IsRollBound (oa : FreeM P α) (budget : B)
    (canRoll : P.A → B → Prop) (cost : P.A → B → B) : Prop :=
  FreeM.rec (motive := fun _ => B → Prop)
    (fun _ _ => True)
    (fun a _r ih b => canRoll a b ∧ ∀ y, ih y (cost a b))
    oa budget

/-- Project an `IsRollBound` along a budget projection `proj : B → B'`.

If the source bound at budget `b` validates rolls at every step, the projected
bound at `proj b` is also validated, provided:
* `h_can`  — whenever a step is allowed in the source (`canRoll a b'`), it is
  allowed in the projection (`canRoll' a (proj b')`);
* `h_cost` — the projection commutes with the cost step on the allowed branch
  (`proj (cost a b') = cost' a (proj b')`). -/
lemma IsRollBound.proj
    {B' : Type*} (proj : B → B')
    {oa : FreeM P α} {b : B}
    {canRoll : P.A → B → Prop} {cost : P.A → B → B}
    {canRoll' : P.A → B' → Prop} {cost' : P.A → B' → B'}
    (h_can : ∀ (a : P.A) (b' : B), canRoll a b' → canRoll' a (proj b'))
    (h_cost : ∀ (a : P.A) (b' : B), canRoll a b' → proj (cost a b') = cost' a (proj b'))
    (h : IsRollBound oa b canRoll cost) :
    IsRollBound oa (proj b) canRoll' cost' := sorry

section Transformers

variable {ε : Type v}

end Transformers

/-- Every query in a finite free program has at least one typed answer, and the
same holds recursively on every answer branch. This is separate from a
branchwise roll bound: universal branch obligations such as `IsTotalRollBound`
are vacuous at a query whose answer type is empty. -/
def ProgramProgress : FreeM P α → Prop
  | .pure _ => True
  | .liftBind a r => Nonempty (P.B a) ∧ ∀ y, ProgramProgress (r y)

/-- Mapping returned values preserves the reachable query tree and hence
program progress. -/
lemma ProgramProgress.map {oa : FreeM P α} (h : oa.ProgramProgress) (f : α → β) :
    (FreeM.map f oa).ProgramProgress := sorry

end PFunctor.FreeM
