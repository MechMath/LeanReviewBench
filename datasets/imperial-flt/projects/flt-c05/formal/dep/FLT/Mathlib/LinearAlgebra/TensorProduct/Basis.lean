module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs

@[expose] public section

open scoped TensorProduct

/-- If A is a nontrivial free R-module and B is a nontrivial R-module then A ⊗[R] B is
  also nontrivial. -/
instance (R : Type*) [CommSemiring R] (A B : Type*) [AddCommMonoid A] [AddCommMonoid B]
    [Module R A] [Module R B] [Module.Free R A] [Nontrivial A] [Nontrivial B] :
    Nontrivial (A ⊗[R] B) := sorry

/-- If A is a nontrivial R-module and B is a nontrivial free R-module then A ⊗[R] B is
  also nontrivial. -/
instance (R : Type*) [CommSemiring R] (A B : Type*) [AddCommMonoid A] [AddCommMonoid B]
    [Module R A] [Module R B] [Module.Free R B] [Nontrivial A] [Nontrivial B] :
    Nontrivial (A ⊗[R] B) := sorry
