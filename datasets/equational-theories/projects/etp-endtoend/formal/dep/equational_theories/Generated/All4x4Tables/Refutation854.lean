
import Mathlib.Data.Finite.Prod
import dep.equational_theories.Equations.All
import dep.equational_theories.FactsSyntax
import dep.equational_theories.MemoFinOp
import dep.equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[4,1,0,2,3],[1,2,0,2,1],[3,2,4,2,3],[3,2,4,2,3],[3,2,4,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
@[implicit_reducible]
def «All4x4Tables [[4,1,0,2,3],[1,2,0,2,1],[3,2,4,2,3],[3,2,4,2,3],[3,2,4,2,3]]» : Magma (Fin 5) where
  op := finOpTable "[[4,1,0,2,3],[1,2,0,2,1],[3,2,4,2,3],[3,2,4,2,3],[3,2,4,2,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[4,1,0,2,3],[1,2,0,2,1],[3,2,4,2,3],[3,2,4,2,3],[3,2,4,2,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [657] [619] :=
    ⟨Fin 5, «All4x4Tables [[4,1,0,2,3],[1,2,0,2,1],[3,2,4,2,3],[3,2,4,2,3],[3,2,4,2,3]]», Finite.of_fintype _, by decideFin!⟩
