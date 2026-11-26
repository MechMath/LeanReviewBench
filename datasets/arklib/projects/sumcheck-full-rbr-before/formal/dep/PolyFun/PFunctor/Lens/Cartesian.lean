module

public import Batteries.Tactic.Lint
public import Cslib.Init
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Util.Notation3
public import dep.PolyFun.PFunctor.Basic
public import dep.PolyFun.PFunctor.Equiv.Basic
public import dep.PolyFun.PFunctor.Lens.Basic
public import dep.PolyFun.PFunctor.Obj
public import dep.dep.CslibCompat.Basic

@[expose] public section

universe u v uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄

namespace PFunctor

namespace Lens

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

/-- A lens `l : Lens P Q` is **cartesian** when every backward fiber
`l.toFunB a : Q.B (l.toFunA a) → P.B a` is a bijection. Equivalently,
`l` is a cartesian morphism in the fibration `Poly → Set` of polynomial
functors over their position sets. -/
def IsCartesian (l : Lens P Q) : Prop :=
  ∀ a, Function.Bijective (l.toFunB a)

namespace IsCartesian

@[simp]
theorem id (P : PFunctor.{uA, uB}) : (Lens.id P).IsCartesian := sorry

theorem comp {l₁ : Lens Q R} {l₂ : Lens P Q}
    (h₁ : l₁.IsCartesian) (h₂ : l₂.IsCartesian) :
    (l₁ ∘ₗ l₂).IsCartesian := sorry

end IsCartesian

namespace IsCartesian

theorem inl {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} :
    (Lens.inl : Lens.{uA₁, uB, max uA₁ uA₂, uB} P (P + Q)).IsCartesian := sorry

theorem inr {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} :
    (Lens.inr : Lens.{uA₂, uB, max uA₁ uA₂, uB} Q (P + Q)).IsCartesian := sorry

theorem sumMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₁}}
    {R : PFunctor.{uA₃, uB₃}} {W : PFunctor.{uA₄, uB₃}}
    {l₁ : Lens P R} {l₂ : Lens Q W}
    (h₁ : l₁.IsCartesian) (h₂ : l₂.IsCartesian) :
    (l₁ ⊎ₗ l₂).IsCartesian
  := sorry

end IsCartesian

namespace IsCartesian

end IsCartesian

end Lens

end PFunctor
