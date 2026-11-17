module

public import Cslib.Init
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Util.Notation3
public import dep.PolyFun.PFunctor.Obj
public import dep.dep.CslibCompat.Basic

@[expose] public section

universe u v uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄ uA₅ uB₅ uA₆ uB₆ vA vB

namespace PFunctor

section Basic

instance : IsEmpty (A 0) := sorry

instance instUniqueAOfNatOne : Unique (A 1) := inferInstanceAs (Unique PUnit)

/-- Parse-only compatibility spelling of the monomial `A y^ B`.

Kept in this foundational module so direct importers of `PFunctor.Basic` or
`PFunctor.Lens.Basic` continue to elaborate while migrating to `y^`. -/
scoped syntax:82 term:83 " X^ " term:82 : term

scoped macro_rules
  | `($A X^ $B) => `(PFunctor.monomial $A $B)

@[deprecated (since := "2026-10-19")] alias representable := purePower

/-- The **universe polynomial functor** `Σ (T : Type u), y^ T`: positions are types,
and the directions at a position `T` are its elements. Its extension `univ.Obj S` is
`Σ (T : Type u), T → S`, so a dynamical system over `univ` is a transition system that
exposes at each state the type of its currently enabled events; see `PFunctor.DynSystem`.

Reducible so that a direction type `univ.B T` unfolds to `T` during elaboration and
instance search, keeping transitions over `univ` as ergonomic as bare functions. -/
@[reducible]
def univ : PFunctor.{u + 1, u} :=
  ⟨Type u, fun T => T⟩

section Coprod

section Sum

/-- The deprecated spelling of `P + Q`. It keeps the body and the `abbrev` transparency it had
before it was deprecated, so instance search and reducible `simp` still compute
`(sum P Q).B (.inl a)` to `P.B a`. cslib's `add` is only implicit-reducible, so a plain alias would
not. -/
@[deprecated add (since := "2026-10-19")]
abbrev sum (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) : PFunctor.{max uA₁ uA₂, uB} :=
  ⟨P.A ⊕ Q.A, @Sum.rec P.A Q.A (fun _ => Type uB) P.B Q.B⟩

/-- The generalized sum (sigma type) of an indexed family of polynomial functors. -/
def sigma {I : Type v} (F : I → PFunctor.{uA, uB}) : PFunctor.{max uA v, uB} :=
  ⟨Σ i, (F i).A, fun ⟨i, a⟩ => (F i).B a⟩

namespace sigma

variable {I : Type v} {F : I → PFunctor.{uA, uB}}

/-- A position of `sigma F`: a family index together with a position of that member.

Use this constructor rather than the anonymous constructor `⟨i, a⟩`, whose type is the
underlying sigma type only after `sigma` unfolds; `sigma.mk i a` has type `(sigma F).A` at
every transparency, so statements about indexed-sum positions elaborate in ordinary-import
consumers and under `linter.tacticCheckInstances`. Apply the projections as `sigma.fst x`
and `sigma.snd x`: generalized field notation on a position resolves to `Sigma.fst` and
`Sigma.snd`, because the position type unfolds to a sigma type. -/
@[implicit_reducible, match_pattern]
def mk (i : I) (a : (F i).A) : (sigma F).A := ⟨i, a⟩

/-- The family index of a position of `sigma F`. -/
@[implicit_reducible] def fst (x : (sigma F).A) : I := x.1

/-- The member position of a position of `sigma F`. -/
@[implicit_reducible] def snd (x : (sigma F).A) : (F (fst x)).A := x.2

/-- To prove a statement about every position of `sigma F`, prove it for `sigma.mk i a`. -/
@[implicit_reducible, elab_as_elim]
def rec {motive : (sigma F).A → Sort*} (mk : ∀ i a, motive (sigma.mk i a)) : ∀ x, motive x :=
  fun x => mk x.1 x.2

@[simp] theorem eta (x : (sigma F).A) : mk (fst x) (snd x) = x := sorry

@[ext] theorem ext {x y : (sigma F).A} (h₁ : fst x = fst y) (h₂ : HEq (snd x) (snd y)) :
    x = y := sorry

theorem mk.inj {i j : I} {a : (F i).A} {b : (F j).A} (h : mk (F := F) i a = mk j b) :
    i = j ∧ HEq a b := sorry

end sigma

/-- `Σₚ i, F i` is the indexed sum `PFunctor.sigma F` of a family of polynomial functors. -/
scoped notation3 "Σₚ "(...)", "F:60:(scoped f => PFunctor.sigma f) => F

end Sum

section Prod

/-- The generalized product (pi type) of an indexed family of polynomial functors. -/
def pi {I : Type v} (F : I → PFunctor.{uA, uB}) : PFunctor.{max uA v, max uB v} :=
  ⟨(i : I) → (F i).A, fun f => Σ i, (F i).B (f i)⟩

/-- `Πₚ i, F i` is the indexed product `PFunctor.pi F` of a family of polynomial functors. -/
scoped notation3 "Πₚ "(...)", "F:60:(scoped f => PFunctor.pi f) => F

end Prod

section Tensor

/-- The tensor (also called parallel or Dirichlet) product of two polynomial functors `P` and `Q`.

Defined as the product of the head types and the product of the child types. -/
def tensor (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) :
    PFunctor.{max uA₁ uA₂, max uB₁ uB₂} :=
  ⟨P.A × Q.A, fun ab => P.B ab.1 × Q.B ab.2⟩

/-- Infix notation for tensor product `P ⊗ Q` -/
scoped[PFunctor] infixl:70 " ⊗ " => tensor

end Tensor

section Comp

/-- Infix notation for `PFunctor.comp P Q` -/
scoped[PFunctor] infixl:80 " ◃ " => PFunctor.comp

/-- The composition power `P ◃^ n`, the `n`-fold composite `P ◃ P ◃ ... ◃ P`. -/
@[simp]
def compNth (P : PFunctor.{uA, uB}) : Nat → PFunctor.{max uA uB, uB}
  | 0 => y
  | Nat.succ n => P ◃ compNth P n

@[inherit_doc] scoped[PFunctor] infixl:85 " ◃^ " => compNth

/-- Compatibility instance for the former `p ^ n` composition-power spelling.
The canonical notation is `p ◃^ n`. -/
instance instNatPowPFunctor : NatPow PFunctor.{max uA uB, uB} where
  pow := compNth

end Comp

section ULift

/-- Lift a polynomial functor `P` to a pair of larger universes. -/
protected def ulift (P : PFunctor.{uA, uB}) : PFunctor.{max uA vA, max uB vB} :=
  ⟨ULift P.A, fun a => ULift (P.B (ULift.down a))⟩

end ULift

/-- Exponential of polynomial functors `P ^ Q` -/
def exp (P Q : PFunctor.{uA, uB}) : PFunctor.{max uA uB, max uA uB} :=
  pi (fun a => P ◃ (y + C (Q.B a)))

instance instHPowPFunctor :
    HPow PFunctor.{uA, uB} PFunctor.{uA, uB} PFunctor.{max uA uB, max uA uB} where
  hPow := exp

section Fintype

/-- A polynomial functor is finitely branching if each of its branches is a finite type. -/
protected class Fintype (P : PFunctor.{uA, uB}) where
  /-- The direction type over each position `a` is a finite type. -/
  fintypeB : ∀ a, Fintype (P.B a)

instance {P : PFunctor.{uA, uB}} [inst : P.Fintype] : PFunctor.Fintype (PFunctor.ulift P) where
  fintypeB := fun a => by
    unfold PFunctor.ulift
    have : Fintype (P.B (ULift.down a)) := inst.fintypeB (ULift.down a)
    infer_instance

@[simp]
instance {P : PFunctor.{uA, uB}} [inst : P.Fintype] : ∀ a, Fintype (P.B a) :=
  fun a => inst.fintypeB a

instance : PFunctor.Fintype 0 where
  fintypeB _ := Fintype.instPEmpty

instance : PFunctor.Fintype 1 where
  fintypeB _ := Fintype.instPEmpty

end Fintype

section Inhabited

/-- A polynomial functor is pointwise inhabited if each of its branches is an inhabited type. -/
protected class Inhabited (P : PFunctor.{uA, uB}) where
  /-- The direction type over each position `a` is inhabited. -/
  inhabitedB : ∀ a, Inhabited (P.B a)

instance {P : PFunctor.{uA, uB}} [inst : P.Inhabited] :
    PFunctor.Inhabited (PFunctor.ulift P) where
  inhabitedB := fun a => by
    unfold PFunctor.ulift
    have : Inhabited (P.B (ULift.down a)) := inst.inhabitedB (ULift.down a)
    infer_instance

@[simp]
instance {P : PFunctor.{uA, uB}} [inst : P.Inhabited] : ∀ a, Inhabited (P.B a) :=
  fun a => inst.inhabitedB a

end Inhabited

section DecidableEq

/-- A polynomial functor has decidable equality if its position type and each of its
direction types have decidable equality. -/
protected class DecidableEq (P : PFunctor.{uA, uB}) where
  /-- The position type `P.A` has decidable equality. -/
  decidableEqA : DecidableEq P.A
  /-- The direction type over each position `a` has decidable equality. -/
  decidableEqB : ∀ a, DecidableEq (P.B a)

instance {P : PFunctor.{uA, uB}} [inst : P.DecidableEq] : DecidableEq P.A :=
  inst.decidableEqA

instance {P : PFunctor.{uA, uB}} [inst : P.DecidableEq] (a : P.A) :
    DecidableEq (P.B a) := inst.decidableEqB a

@[simp]
instance {P : PFunctor.{uA, uB}} [inst : P.DecidableEq] :
    PFunctor.DecidableEq (PFunctor.ulift P) where
  decidableEqA := by
    unfold PFunctor.ulift
    infer_instance
  decidableEqB := fun a => by
    unfold PFunctor.ulift
    infer_instance

instance : PFunctor.DecidableEq 0 where
  decidableEqA := inferInstanceAs (DecidableEq PEmpty)
  decidableEqB _ := inferInstanceAs (DecidableEq PEmpty)

instance : PFunctor.DecidableEq 1 where
  decidableEqA := inferInstanceAs (DecidableEq PUnit)
  decidableEqB _ := inferInstanceAs (DecidableEq PEmpty)

end DecidableEq

section monomial

variable (A : Type uA) (B : Type uB)

instance [Fintype B] : (monomial A B).Fintype where
  fintypeB _ := inferInstanceAs (Fintype B)

instance [DecidableEq A] [DecidableEq B] : (monomial A B).DecidableEq where
  decidableEqA := inferInstanceAs (DecidableEq A)
  decidableEqB _ := inferInstanceAs (DecidableEq B)

instance [Inhabited B] : (monomial A B).Inhabited where
  inhabitedB _ := inferInstanceAs (Inhabited B)

end monomial

/-- An equivalence between two polynomial functors `P` and `Q`, written `P ≃ₚ Q`, is given by an
equivalence of the `A` types and an equivalence between the `B` types for each `a : A`. -/
@[ext]
protected structure Equiv (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) where
  /-- An equivalence between the `A` types -/
  equivA : P.A ≃ Q.A
  /-- An equivalence between the `B` types for each `a : A` -/
  equivB : ∀ a, P.B a ≃ Q.B (equivA a)

@[inherit_doc] scoped[PFunctor] infixl:25 " ≃ₚ " => PFunctor.Equiv

namespace Equiv

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}

/-- The identity equivalence between a polynomial functor `P` and itself. -/
@[refl, simps]
def refl (P : PFunctor.{uA, uB}) : P ≃ₚ P where
  equivA := _root_.Equiv.refl P.A
  equivB := fun a => _root_.Equiv.refl (P.B a)

/-- The inverse of an equivalence between polynomial functors. Its direction equivalences are
transported along `E.equivA.apply_symm_apply`, so only its position equivalence is a `simp`
projection (`symm_equivA`). -/
@[symm]
def symm {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (E : P ≃ₚ Q) : Q ≃ₚ P where
  equivA := E.equivA.symm
  equivB := fun a =>
    (Equiv.cast (congrArg Q.B ((Equiv.symm_apply_eq E.equivA).mp rfl))).trans
      (E.equivB (E.equivA.symm a)).symm

/-- The composition of two equivalences between polynomial functors. -/
@[trans, simps]
def trans {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (E : P ≃ₚ Q) (F : Q ≃ₚ R) : P ≃ₚ R where
  equivA := E.equivA.trans F.equivA
  equivB := fun a => (E.equivB a).trans (F.equivB (E.equivA a))

/-- Polynomial equivalences compose in `calc` chains, across independent universes. -/
instance instTrans :
    @Trans PFunctor.{uA₁, uB₁} PFunctor.{uA₂, uB₂} PFunctor.{uA₃, uB₃}
      PFunctor.Equiv PFunctor.Equiv PFunctor.Equiv where
  trans := Equiv.trans

/-- Equivalence between two polynomial functors `P` and `Q` that are equal. -/
def cast {P Q : PFunctor.{uA, uB}} (hA : P.A = Q.A) (hB : ∀ a, P.B a = Q.B (cast hA a)) :
    P ≃ₚ Q where
  equivA := _root_.Equiv.cast hA
  equivB := fun a => _root_.Equiv.cast (hB a)

theorem symm_equivA_comp_equivA {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    (e : P ≃ₚ Q) : e.symm.equivA ∘ e.equivA = id := sorry

@[deprecated (since := "2026-10-19")] alias symm_comp_self := symm_equivA_comp_equivA

/-- Applying `equivB` and then `symm.equivB` gives a cast. -/
lemma symm_equivB_equivB (e : P ≃ₚ Q) (a : P.A) (b : P.B a) :
    e.symm.equivB (e.equivA a) (e.equivB a b) =
      _root_.cast (congrArg P.B (e.equivA.symm_apply_apply a).symm) b := sorry

@[deprecated (since := "2026-10-19")] alias forward_equivB_roundtrip := symm_equivB_equivB

/-- Applying `symm.equivB` and then `equivB` gives a cast. -/
lemma equivB_symm_equivB (e : P ≃ₚ Q) (a : Q.A)
    (b : Q.B a) :
    e.equivB (e.equivA.symm a) (e.symm.equivB a b) =
      _root_.cast
        (congrArg Q.B (e.equivA.apply_symm_apply a).symm) b := sorry

@[deprecated (since := "2026-10-19")] alias reverse_equivB_roundtrip := equivB_symm_equivB

end Equiv

/-- A **lens** between two polynomial functors `P` and `Q` is a pair of a function:
- `toFunA : P.A → Q.A`
- `toFunB : ∀ a, Q.B (toFunA a) → P.B a` -/
structure Lens (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) where
  /-- The forward map on positions, sending each position of `P` to a position of `Q`. -/
  toFunA : P.A → Q.A
  /-- The backward map on directions, pulling a direction of `Q` at `toFunA a` back to a
  direction of `P` at `a`. -/
  toFunB : ∀ a, Q.B (toFunA a) → P.B a

/-- Infix notation for constructing a lens `toFunA ⇆ toFunB`; activate it with
`open scoped PFunctor`. -/
scoped infixr:25 " ⇆ " => Lens.mk

/-- A chart between two polynomial functors `P` and `Q` is a pair of a function:
- `toFunA : P.A → Q.A`
- `toFunB : ∀ a, P.B a → Q.B (toFunA a)` -/
structure Chart (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) where
  /-- The forward map on positions, sending each position of `P` to a position of `Q`. -/
  toFunA : P.A → Q.A
  /-- The forward map on directions, pushing a direction of `P` at `a` to a direction of `Q`
  at `toFunA a`. -/
  toFunB : ∀ a, P.B a → Q.B (toFunA a)

/-- Infix notation for constructing a chart `toFunA ⇉ toFunB`; activate it with
`open scoped PFunctor`. -/
scoped infixr:25 " ⇉ " => Chart.mk

section Lemmas

section ULift

variable {P : PFunctor.{uA, uB}}

end ULift

end Lemmas

end Coprod

end Basic

end PFunctor
