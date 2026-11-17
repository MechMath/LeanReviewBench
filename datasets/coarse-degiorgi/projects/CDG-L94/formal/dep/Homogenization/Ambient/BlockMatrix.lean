module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import dep.Homogenization.Ambient.Basic

@[expose] public section

namespace Homogenization

abbrev BlockCoord (d : ℕ) := Sum (Fin d) (Fin d)

/-- File-level typeclass cache for `Nonempty (BlockCoord d)`. -/
private instance instNonemptyBlockCoord (d : ℕ) [NeZero d] :
    Nonempty (BlockCoord d) := sorry

/--
Löwner order on finite-dimensional real matrices, expressed through the quadratic
form `\frac12 x \cdot A x`.
-/
def MatLoewnerLE {d : ℕ} (A B : Mat d) : Prop :=
  ∀ x : Vec d,
    (1 / 2 : ℝ) * vecDot x (matVecMul A x) ≤
      (1 / 2 : ℝ) * vecDot x (matVecMul B x)

/--
Löwner order on doubled block matrices, expressed through the quadratic form
`\frac12 X \cdot \mathbf A X`.
-/
def BlockMatLoewnerLE {d : ℕ} (A B : BlockMat d) : Prop :=
  ∀ X : BlockVec d,
    (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul A X) ≤
      (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul B X)

theorem MatLoewnerLE.trans {d : ℕ} {A B C : Mat d}
    (hAB : MatLoewnerLE A B) (hBC : MatLoewnerLE B C) :
    MatLoewnerLE A C := sorry

theorem BlockMatLoewnerLE.trans {d : ℕ} {A B C : BlockMat d}
    (hAB : BlockMatLoewnerLE A B) (hBC : BlockMatLoewnerLE B C) :
    BlockMatLoewnerLE A C := sorry

end Homogenization
