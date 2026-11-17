module

public import Mathlib.Data.PFunctor.Univariate.Basic

public section

namespace PFunctor.Obj

universe uA uB u

variable {P : PFunctor.{uA, uB}} {α : Type u}

/-- Polynomial objects are equal when their shapes and child families agree. -/
@[ext]
theorem ext {x y : P α} (h : x.fst = y.fst) (h' : HEq x.snd y.snd) : x = y := sorry

/-- Equal constructed polynomial objects have equal shapes and child families. -/
theorem mk.inj {a b : P.A} {f : P.B a → α} {g : P.B b → α}
    (h : Obj.mk a f = Obj.mk b g) : a = b ∧ HEq f g := sorry

end PFunctor.Obj
