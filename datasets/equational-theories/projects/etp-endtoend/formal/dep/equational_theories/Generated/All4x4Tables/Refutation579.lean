
import Mathlib.Data.Finite.Prod
import dep.equational_theories.Equations.All
import dep.equational_theories.FactsSyntax
import dep.equational_theories.MemoFinOp
import dep.equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,2,3],[1,1,2,3],[0,0,2,3],[2,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
@[implicit_reducible]
def «All4x4Tables [[1,1,2,3],[1,1,2,3],[0,0,2,3],[2,1,2,3]]» : Magma (Fin 4) where
  op := finOpTable "[[1,1,2,3],[1,1,2,3],[0,0,2,3],[2,1,2,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,1,2,3],[1,1,2,3],[0,0,2,3],[2,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [4209] [3887] :=
    ⟨Fin 4, «All4x4Tables [[1,1,2,3],[1,1,2,3],[0,0,2,3],[2,1,2,3]]», Finite.of_fintype _, by decideFin!⟩
