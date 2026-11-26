module

public import Batteries.Tactic.Lint
public import Cslib.Init
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Util.Notation3
public import dep.PolyFun.PFunctor.Basic
public import dep.PolyFun.PFunctor.Equiv.Basic
public import dep.PolyFun.PFunctor.Obj
public import dep.dep.CslibCompat.Basic

@[expose] public section

universe u v uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄ uA₅ uB₅ uA₆ uB₆

section find_home

variable {α : Sort u} {β : α → Sort v} {γ : α → Sort v}

end find_home

namespace PFunctor

namespace Lens

/-- Lenses agree when their position maps agree pointwise and their direction maps agree after
transport along those position equalities. -/
@[ext (iff := false)]
theorem ext {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (l₁ l₂ : Lens P Q)
    (h₁ : ∀ a, l₁.toFunA a = l₂.toFunA a) (h₂ : ∀ a, l₁.toFunB a = (h₁ a) ▸ l₂.toFunB a) :
    l₁ = l₂ := sorry

/-- The identity lens -/
@[reducible]
protected def id (P : PFunctor.{uA, uB}) : Lens P P where
  toFunA := fun a => a
  toFunB := fun _ b => b

/-- Composition of lenses -/
def comp {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (l : Lens Q R) (l' : Lens P Q) : Lens P R where
  toFunA := l.toFunA ∘ l'.toFunA
  toFunB := fun i => (l'.toFunB i) ∘ l.toFunB (l'.toFunA i)

@[inherit_doc] scoped[PFunctor] infixl:75 " ∘ₗ " => PFunctor.Lens.comp

/-- An equivalence between two polynomial functors `P` and `Q`, using lenses.
    This corresponds to an isomorphism in the category `PFunctor` with `Lens` morphisms. -/
@[ext]
structure Equiv (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) where
  /-- The forward lens of the equivalence, from `P` to `Q`. -/
  toLens : Lens P Q
  /-- The backward lens of the equivalence, from `Q` to `P`. -/
  invLens : Lens Q P
  left_inv : comp invLens toLens = Lens.id P := by simp
  right_inv : comp toLens invLens = Lens.id Q := by simp

@[inherit_doc] scoped[PFunctor] infix:50 " ≃ₗ " => PFunctor.Lens.Equiv

namespace Equiv

/-- The identity equivalence on `P`, built from the identity lens in both directions. -/
@[refl, simps]
def refl (P : PFunctor.{uA, uB}) : P ≃ₗ P :=
  ⟨Lens.id P, Lens.id P, rfl, rfl⟩

/-- The inverse equivalence, swapping the forward and backward lenses of `e`. -/
@[symm, simps]
def symm {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (e : P ≃ₗ Q) : Q ≃ₗ P :=
  ⟨e.invLens, e.toLens, e.right_inv, e.left_inv⟩

/-- The composite equivalence `P ≃ₗ R` obtained by chaining `e₁ : P ≃ₗ Q` and `e₂ : Q ≃ₗ R`. -/
@[trans, simps]
def trans {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (e₁ : P ≃ₗ Q) (e₂ : Q ≃ₗ R) : P ≃ₗ R :=
  ⟨e₂.toLens ∘ₗ e₁.toLens, e₁.invLens ∘ₗ e₂.invLens,
    sorry,
    sorry⟩

/-- Lens equivalences compose in `calc` chains, across independent universes. -/
instance instTrans :
    @Trans PFunctor.{uA₁, uB₁} PFunctor.{uA₂, uB₂} PFunctor.{uA₃, uB₃}
      Lens.Equiv Lens.Equiv Lens.Equiv where
  trans := Equiv.trans

section Groupoid

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
  {S : PFunctor.{uA₄, uB₄}}

end Groupoid

end Equiv

/-- The (unique) initial lens from the zero functor to any functor `P`. -/
def initial {P : PFunctor.{uA, uB}} : Lens 0 P :=
  PEmpty.elim ⇆ fun a => PEmpty.elim a

/-- The (unique) terminal lens from any functor `P` to the unit functor `1`. -/
def terminal {P : PFunctor.{uA, uB}} : Lens P 1 :=
  (fun _ => PUnit.unit) ⇆ fun _ => PEmpty.elim

/-- `0` is initial: `initial` is the only lens out of it. -/
instance uniqueFromZero {P : PFunctor.{uA, uB}} :
    Unique (Lens (0 : PFunctor.{uA₁, uB₁}) P) where
  default := initial
  uniq _ := Lens.ext _ _ (fun a => a.elim) fun a => a.elim

/-- `1` is terminal: `terminal` is the only lens into it. -/
instance uniqueToOne {P : PFunctor.{uA, uB}} :
    Unique (Lens P (1 : PFunctor.{uA₁, uB₁})) where
  default := terminal
  uniq _ := Lens.ext _ _ (fun _ => rfl) fun _ => funext fun d => d.elim

/-- Left injection lens `inl : P → P + Q` -/
def inl {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} :
    Lens.{uA₁, uB, max uA₁ uA₂, uB} P (P + Q) :=
  Sum.inl ⇆ fun _ => id

/-- Right injection lens `inr : Q → P + Q` -/
def inr {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} :
    Lens.{uA₂, uB, max uA₁ uA₂, uB} Q (P + Q) :=
  Sum.inr ⇆ fun _ => id

/-- Copairing of lenses `[l₁, l₂]ₗ : P + Q → R` -/
def sumPair {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} {R : PFunctor.{uA₃, uB₃}}
    (l₁ : Lens P R) (l₂ : Lens Q R) :
    Lens.{max uA₁ uA₂, uB, uA₃, uB₃} (P + Q) R :=
  Sum.elim l₁.toFunA l₂.toFunA ⇆ fun
    | .inl pa => l₁.toFunB pa
    | .inr qa => l₂.toFunB qa

/-- Parallel application of lenses for coproduct `l₁ ⊎ l₂ : P + Q → R + W` -/
def sumMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₁}} {R : PFunctor.{uA₃, uB₃}}
    {W : PFunctor.{uA₄, uB₃}} (l₁ : Lens P R) (l₂ : Lens Q W) :
    Lens.{max uA₁ uA₂, uB₁, max uA₃ uA₄, uB₃} (P + Q) (R + W) :=
  Sum.map l₁.toFunA l₂.toFunA ⇆ fun
    | .inl pa => l₁.toFunB pa
    | .inr qa => l₂.toFunB qa

/-- Projection lens `fst : P * Q → P` -/
def fst {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} :
    Lens.{max uA₁ uA₂, max uB₁ uB₂, uA₁, uB₁} (P * Q) P :=
  Prod.fst ⇆ fun _ => Sum.inl

/-- Projection lens `snd : P * Q → Q` -/
def snd {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} :
    Lens.{max uA₁ uA₂, max uB₁ uB₂, uA₂, uB₂} (P * Q) Q :=
  Prod.snd ⇆ fun _ => Sum.inr

/-- Pairing of lenses `⟨l₁, l₂⟩ₗ : P → Q * R` -/
def prodPair {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (l₁ : Lens P Q) (l₂ : Lens P R) :
    Lens.{uA₁, uB₁, max uA₂ uA₃, max uB₂ uB₃} P (Q * R) :=
  (fun p => (l₁.toFunA p, l₂.toFunA p)) ⇆
    (fun p => Sum.elim (l₁.toFunB p) (l₂.toFunB p))

/-- Parallel application of lenses for product `l₁ ×ₗ l₂ : P * Q → R * W` -/
def prodMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    {W : PFunctor.{uA₄, uB₄}} (l₁ : Lens P R) (l₂ : Lens Q W) :
    Lens.{max uA₁ uA₂, max uB₁ uB₂, max uA₃ uA₄, max uB₃ uB₄} (P * Q) (R * W) :=
  (fun pq => (l₁.toFunA pq.1, l₂.toFunA pq.2)) ⇆
    (fun pq => Sum.elim (Sum.inl ∘ l₁.toFunB pq.1) (Sum.inr ∘ l₂.toFunB pq.2))

/-- Apply lenses to both sides of a composition: `l₁ ◃ₗ l₂ : (P ◃ Q ⇆ R ◃ W)` -/
def compMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    {W : PFunctor.{uA₄, uB₄}} (l₁ : Lens P R) (l₂ : Lens Q W) :
    Lens.{max uA₁ uA₂ uB₁, max uB₁ uB₂, max uA₃ uA₄ uB₃, max uB₃ uB₄} (P ◃ Q) (R ◃ W) :=
  (fun ⟨pa, pq⟩ => ⟨l₁.toFunA pa, fun rb' => l₂.toFunA (pq (l₁.toFunB pa rb'))⟩) ⇆
    (fun ⟨pa, pq⟩ ⟨rb, wc⟩ =>
      let pb := l₁.toFunB pa rb
      let qc := l₂.toFunB (pq pb) wc
      ⟨pb, qc⟩)

/-- Apply lenses to both sides of a tensor / parallel product: `l₁ ⊗ₗ l₂ : (P ⊗ Q ⇆ R ⊗ W)` -/
@[implicit_reducible]
def tensorMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    {W : PFunctor.{uA₄, uB₄}} (l₁ : Lens P R) (l₂ : Lens Q W) :
    Lens.{max uA₁ uA₂, max uB₁ uB₂, max uA₃ uA₄, max uB₃ uB₄} (P ⊗ Q) (R ⊗ W) :=
  Prod.map l₁.toFunA l₂.toFunA ⇆
    fun (pa, qa) => Prod.map (l₁.toFunB pa) (l₂.toFunB qa)

@[inherit_doc] scoped[PFunctor] infixl:75 " ◃ₗ " => PFunctor.Lens.compMap

@[inherit_doc] scoped[PFunctor] infixl:75 " ×ₗ " => PFunctor.Lens.prodMap

@[inherit_doc] scoped[PFunctor] infixl:75 " ⊎ₗ " => PFunctor.Lens.sumMap

@[inherit_doc] scoped[PFunctor] infixl:75 " ⊗ₗ " => PFunctor.Lens.tensorMap

/-- Notation for the copairing `sumPair l₁ l₂` of two lenses out of a sum; activate it with
`open scoped PFunctor.Lens`. -/
scoped notation "[" l₁ "," l₂ "]ₗ" => sumPair l₁ l₂

/-- Notation for the pairing `prodPair l₁ l₂` of two lenses into a product; activate it with
`open scoped PFunctor.Lens`. -/
scoped notation "⟨" l₁ "," l₂ "⟩ₗ" => prodPair l₁ l₂

section Coprod

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₁}}
  {R : PFunctor.{uA₃, uB₃}} {W : PFunctor.{uA₄, uB₃}} {V : PFunctor.{uA₅, uB₅}}

namespace Equiv

variable {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} {R : PFunctor.{uA₃, uB}}

end Equiv

end Coprod

section Prod

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
  {W : PFunctor.{uA₄, uB₄}} {V : PFunctor.{uA₅, uB₅}}

namespace Equiv

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

variable {R : PFunctor.{uA₃, uB₂}}

end Equiv

end Prod

section Comp

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

namespace Equiv

end Equiv

end Comp

section Tensor

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

namespace Equiv

variable {R : PFunctor.{uA₃, uB₂}}

end Equiv

end Tensor

end Lens

namespace Equiv

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}

/-- Convert an equivalence between two polynomial functors `P` and `Q` to a lens. -/
def toLensEquiv (e : P ≃ₚ Q) : P ≃ₗ Q where
  toLens := e.equivA ⇆ (fun a => (e.equivB a).symm)
  invLens := e.symm.equivA ⇆ (fun a => (e.symm.equivB a).symm)
  left_inv := sorry
  right_inv := sorry

end Equiv

namespace Lens

section Sigma

variable {I : Type v}

instance [IsEmpty I] {F : I → PFunctor.{u}} : IsEmpty (sigma F).A := sorry

instance [IsEmpty I] {F : I → PFunctor.{u}} {a : (sigma F).A} : IsEmpty ((sigma F).B a) := sorry

/-- Sigma of an empty family is the zero functor. -/
def Equiv.emptySigma [IsEmpty I] {F : I → PFunctor.{uA, uB}} : sigma F ≃ₗ 0 :=
  PFunctor.Equiv.toLensEquiv (PFunctor.Equiv.emptySigma (F := F))

@[deprecated (since := "2026-10-19")] alias sigmaEmpty := Equiv.emptySigma

/-- Sigma of a `PUnit`-indexed family is equivalent to the functor itself (up to `ulift`). -/
def Equiv.punitSigma {F : PUnit → PFunctor.{uA, uB}} : sigma F ≃ₗ (F PUnit.unit).ulift :=
  PFunctor.Equiv.toLensEquiv
    (PFunctor.Equiv.trans
      (PFunctor.Equiv.punitSigma (F := F))
      (PFunctor.Equiv.ulift (F PUnit.unit)).symm)

@[deprecated (since := "2026-10-19")] alias sigmaUnit := Equiv.punitSigma

/-- Sigma of a unique-indexed family is equivalent to the default fiber (up to `ulift`). -/
def Equiv.uniqueSigma [Unique I] {F : I → PFunctor.{uA, uB}} : sigma F ≃ₗ (F default).ulift :=
  PFunctor.Equiv.toLensEquiv
    (PFunctor.Equiv.trans
      (PFunctor.Equiv.uniqueSigma (F := F))
      (PFunctor.Equiv.ulift (F default)).symm)

@[deprecated (since := "2026-10-19")] alias sigmaOfUnique := Equiv.uniqueSigma

/-- Left distributivity of product over sigma. -/
def Equiv.prodSigmaDistrib {P : PFunctor.{uA₁, uB₁}} {F : I → PFunctor.{uA₂, uB₂}} :
    (P * sigma F : PFunctor.{max uA₁ uA₂ v, max uB₁ uB₂}) ≃ₗ
      (sigma (fun i => (P * F i : PFunctor.{max uA₁ uA₂, max uB₁ uB₂})) :
        PFunctor.{max uA₁ uA₂ v, max uB₁ uB₂}) :=
  PFunctor.Equiv.toLensEquiv (PFunctor.Equiv.prodSigmaDistrib (P := P) (F := F))

@[deprecated (since := "2026-10-19")] alias prodSigmaDistrib := Equiv.prodSigmaDistrib

/-- Right distributivity of product over sigma. -/
def Equiv.sigmaProdDistrib {P : PFunctor.{uA₁, uB₁}} {F : I → PFunctor.{uA₂, uB₂}} :
    (sigma F * P : PFunctor.{max uA₁ uA₂ v, max uB₁ uB₂}) ≃ₗ
      (sigma (fun i => (F i * P : PFunctor.{max uA₁ uA₂, max uB₁ uB₂})) :
        PFunctor.{max uA₁ uA₂ v, max uB₁ uB₂}) :=
  PFunctor.Equiv.toLensEquiv (PFunctor.Equiv.sigmaProdDistrib (P := P) (F := F))

@[deprecated (since := "2026-10-19")] alias sigmaProdDistrib := Equiv.sigmaProdDistrib

/-- Left distributivity of tensor product over sigma. -/
def Equiv.tensorSigmaDistrib {P : PFunctor.{uA₁, uB₁}} {F : I → PFunctor.{uA₂, uB₂}} :
    P ⊗ sigma F ≃ₗ sigma (fun i => P ⊗ F i) :=
  PFunctor.Equiv.toLensEquiv (PFunctor.Equiv.tensorSigmaDistrib (P := P) (F := F))

@[deprecated (since := "2026-10-19")] alias tensorSigmaDistrib := Equiv.tensorSigmaDistrib

/-- Right distributivity of tensor product over sigma. -/
def Equiv.sigmaTensorDistrib {P : PFunctor.{uA₂, uB₂}} {F : I → PFunctor.{uA₁, uB₁}} :
    sigma F ⊗ P ≃ₗ sigma (fun i => F i ⊗ P) :=
  PFunctor.Equiv.toLensEquiv (PFunctor.Equiv.sigmaTensorDistrib (F := F) (P := P))

@[deprecated (since := "2026-10-19")] alias sigmaTensorDistrib := Equiv.sigmaTensorDistrib

/-- Right distributivity of composition over sigma. -/
def Equiv.sigmaCompDistrib {P : PFunctor.{uA₂, uB₂}} {F : I → PFunctor.{uA₁, uB₁}} :
    sigma F ◃ P ≃ₗ sigma (fun i => F i ◃ P) :=
  PFunctor.Equiv.toLensEquiv (PFunctor.Equiv.sigmaCompDistrib (F := F) (P := P))

@[deprecated (since := "2026-10-19")] alias sigmaCompDistrib := Equiv.sigmaCompDistrib

end Sigma

section Pi

variable {I : Type v}

/-- Pi over a `PUnit`-indexed family is equivalent to the functor itself. -/
def Equiv.piPUnit {P : PFunctor.{u}} : pi (fun (_ : PUnit) => P) ≃ₗ P where
  toLens := (fun f => f PUnit.unit) ⇆ (fun _ pb => ⟨PUnit.unit, pb⟩)
  invLens := (fun pa _ => pa) ⇆ (fun _ spb => spb.2)
  left_inv := rfl
  right_inv := rfl

@[deprecated (since := "2026-10-19")] alias piUnit := Equiv.piPUnit

/-- Pi of a family of zero functors over an inhabited type is the zero functor. -/
def Equiv.piZero [Inhabited I] {F : I → PFunctor.{uA, uB}} (F_zero : ∀ i, F i = 0) :
    pi F ≃ₗ 0 := by
  have : IsEmpty (pi F).A := by
    refine ⟨fun f => ?_⟩
    have hf : (F default).A := f default
    rw [F_zero (default : I)] at hf
    exact hf.elim
  refine
    { toLens := isEmptyElim ⇆ fun a => isEmptyElim a
      invLens := PEmpty.elim ⇆ fun a => PEmpty.elim a
      left_inv := sorry
      right_inv := sorry }

@[deprecated (since := "2026-10-19")] alias piZero := Equiv.piZero

end Pi

namespace Equiv

/-- ULift equivalence for lenses -/
def ulift {P : PFunctor.{uA, uB}} : P.ulift ≃ₗ P where
  toLens := ULift.down ⇆ fun _ => ULift.up
  invLens := ULift.up ⇆ fun _ => ULift.down
  left_inv := rfl
  right_inv := rfl

end Equiv

end Lens

end PFunctor
