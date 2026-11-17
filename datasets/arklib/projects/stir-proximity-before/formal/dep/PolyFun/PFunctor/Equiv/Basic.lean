module

public import Cslib.Init
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Util.Notation3
public import dep.PolyFun.PFunctor.Basic
public import dep.PolyFun.PFunctor.Obj
public import dep.dep.CslibCompat.Basic

@[expose] public section

universe u v uA uB uA' uB' uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄

section find_home

instance PSigma.isEmpty_left {α : Sort u} {β : α → Sort v} [inst : IsEmpty α] :
    IsEmpty ((a : α) ×' β a) := sorry

end find_home

namespace PFunctor

namespace Equiv

section Sum

variable (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB})
  (R : PFunctor.{uA₃, uB}) (S : PFunctor.{uA₄, uB})

end Sum

section Prod

variable (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) (R : PFunctor.{uA₃, uB₃})
  (S : PFunctor.{uA₄, uB₄})

end Prod

section Sigma

variable (P : PFunctor.{uA₁, uB₁}) {I : Type v} (F : I → PFunctor.{uA₂, uB₂})

instance [inst : IsEmpty I] : IsEmpty (sigma F).A := sorry

/-- Sigma of an empty family is the zero functor. -/
def emptySigma [inst : IsEmpty I] : sigma F ≃ₚ 0 where
  equivA := Equiv.equivPEmpty _
  equivB := fun a => inst.elim a.1

/-- Sigma over a subsingleton index type is the single functor `F default`. -/
def uniqueSigma [Unique I] : sigma F ≃ₚ F default where
  equivA := _root_.Equiv.uniqueSigma _
  equivB := fun ⟨i, a⟩ => by
    have hi := Unique.eq_default i
    subst hi
    exact _root_.Equiv.refl _

/-- Sigma of a `PUnit`-indexed family is equivalent to the functor itself. -/
def punitSigma {F : PUnit → PFunctor.{uA, uB}} : sigma F ≃ₚ F PUnit.unit where
  equivA := _root_.Equiv.uniqueSigma _
  equivB := fun ⟨i, a⟩ => by cases i; exact _root_.Equiv.refl _

/-- Left distributivity of product over sigma. -/
def prodSigmaDistrib : (P * sigma F : PFunctor.{max uA₁ uA₂ v, max uB₁ uB₂}) ≃ₚ
    sigma (fun i => (P * F i : PFunctor.{max uA₁ uA₂, max uB₁ uB₂})) where
  equivA := {
    toFun := fun ⟨pa, ⟨i, fa⟩⟩ => ⟨i, ⟨pa, fa⟩⟩
    invFun := fun ⟨i, ⟨pa, fa⟩⟩ => ⟨pa, ⟨i, fa⟩⟩
    left_inv := sorry
    right_inv := sorry
  }
  equivB := fun a => by
    rcases a with ⟨pa, ⟨i, fa⟩⟩
    exact _root_.Equiv.refl _

/-- Right distributivity of product over sigma. -/
def sigmaProdDistrib : (sigma F * P : PFunctor.{max uA₁ uA₂ v, max uB₁ uB₂}) ≃ₚ
    sigma (fun i => (F i * P : PFunctor.{max uA₁ uA₂, max uB₁ uB₂})) where
  equivA := {
    toFun := fun ⟨⟨i, fa⟩, pa⟩ => ⟨i, ⟨fa, pa⟩⟩
    invFun := fun ⟨i, ⟨fa, pa⟩⟩ => ⟨⟨i, fa⟩, pa⟩
    left_inv := sorry
    right_inv := sorry
  }
  equivB := fun a => by
    rcases a with ⟨⟨i, fa⟩, pa⟩
    exact _root_.Equiv.refl _

/-- Left distributivity of tensor product over sigma. -/
def tensorSigmaDistrib :
    P ⊗ sigma F ≃ₚ sigma (fun i => P ⊗ F i) where
  equivA := {
    toFun := fun ⟨pa, ⟨i, fa⟩⟩ => ⟨i, ⟨pa, fa⟩⟩
    invFun := fun ⟨i, ⟨pa, fa⟩⟩ => ⟨pa, ⟨i, fa⟩⟩
    left_inv := sorry
    right_inv := sorry
  }
  equivB := fun a => by
    rcases a with ⟨pa, ⟨i, fa⟩⟩
    exact _root_.Equiv.refl _

/-- Right distributivity of tensor product over sigma. -/
def sigmaTensorDistrib {I : Type v} (F : I → PFunctor.{uA₁, uB₁}) (P : PFunctor.{uA₂, uB₂}) :
    sigma F ⊗ P ≃ₚ sigma (fun i => F i ⊗ P) where
  equivA := {
    toFun := fun ⟨⟨i, fa⟩, pa⟩ => ⟨i, ⟨fa, pa⟩⟩
    invFun := fun ⟨i, ⟨fa, pa⟩⟩ => ⟨⟨i, fa⟩, pa⟩
    left_inv := sorry
    right_inv := sorry
  }
  equivB := fun a => by
    rcases a with ⟨⟨i, fa⟩, pa⟩
    exact _root_.Equiv.refl _

/-- Right distributivity of composition over sigma. -/
def sigmaCompDistrib {I : Type v} (F : I → PFunctor.{uA₁, uB₁}) (P : PFunctor.{uA₂, uB₂}) :
    sigma F ◃ P ≃ₚ sigma (fun i => F i ◃ P) where
  equivA := {
    toFun := fun ⟨⟨i, fa⟩, pf⟩ => ⟨i, ⟨fa, pf⟩⟩
    invFun := fun ⟨i, ⟨fa, pf⟩⟩ => ⟨⟨i, fa⟩, pf⟩
    left_inv := sorry
    right_inv := sorry
  }
  equivB := fun a => by
    rcases a with ⟨⟨i, fa⟩, pf⟩
    exact _root_.Equiv.refl _

end Sigma

section Pi

end Pi

section ULift

variable (P : PFunctor.{uA₁, uB₁})

/-- The universe lift of a polynomial functor is equivalent to the polynomial functor. -/
def ulift : (P.ulift : PFunctor.{max uA₁ u, max uB₁ v}) ≃ₚ P where
  equivA := _root_.Equiv.ulift
  equivB := fun _ => _root_.Equiv.ulift

end ULift

section Tensor

variable (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) (R : PFunctor.{uA₃, uB₃})
  (S : PFunctor.{uA₄, uB₄})

instance {P} {a : (P ⊗ 1).A} : IsEmpty ((P ⊗ 1).B a) := sorry

instance {P} {a : (1 ⊗ P).A} : IsEmpty ((1 ⊗ P).B a) := sorry

end Tensor

section Comp

variable (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) (R : PFunctor.{uA₃, uB₃})

instance : IsEmpty (0 ◃ P).A := sorry

instance {a : (1 ◃ P).A} : IsEmpty ((1 ◃ P).B a) := sorry

end Comp

end Equiv

end PFunctor
