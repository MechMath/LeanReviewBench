
import Mathlib.Data.Finite.Prod
import dep.equational_theories.Equations.All
import dep.equational_theories.FactsSyntax
import dep.equational_theories.MemoFinOp
import dep.equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,3,3],[2,1,2,3],[0,3,2,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
@[implicit_reducible]
def «All4x4Tables [[0,2,3,3],[2,1,2,3],[0,3,2,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := finOpTable "[[0,2,3,3],[2,1,2,3],[0,3,2,3],[0,1,2,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,2,3,3],[2,1,2,3],[0,3,2,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2584, 2973] [1691, 2669, 3306, 3512, 3925, 4155] :=
    ⟨Fin 4, «All4x4Tables [[0,2,3,3],[2,1,2,3],[0,3,2,3],[0,1,2,3]]», Finite.of_fintype _, by decideFin!⟩
