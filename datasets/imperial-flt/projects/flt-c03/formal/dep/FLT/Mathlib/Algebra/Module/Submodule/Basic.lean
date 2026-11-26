module

public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic

@[expose] public section

variable {R S : Type*} [Ring R]

/-- If `S` is a subring of `R`, then `S` can be viewed as an `S`-submodule of `R`. -/
def Subring.toSubmodule (S : Subring R) : Submodule S R where
  __ := S
  smul_mem' x y h := sorry
