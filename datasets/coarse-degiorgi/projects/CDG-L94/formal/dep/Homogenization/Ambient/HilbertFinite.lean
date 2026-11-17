module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.InnerProductSpace.PiL2
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
public import dep.Homogenization.Ambient.BlockMatrix

@[expose] public section

namespace Homogenization

/-- The Euclidean Hilbert realization of `\R^d`, presented without exposing
`EuclideanSpace` in the public API. -/
abbrev HilbertVec (d : ℕ) := PiLp 2 (fun _ : Fin d => ℝ)

namespace HilbertVec

/-- Promote the project's algebraic vector carrier into the Euclidean Hilbert
carrier. -/
abbrev ofVec {d : ℕ} (x : Vec d) : HilbertVec d :=
  WithLp.toLp 2 x

/-- Forget the Hilbert structure and return to the project's algebraic vector
carrier. -/
abbrev toVec {d : ℕ} (x : HilbertVec d) : Vec d :=
  fun i => x i

@[simp] theorem toVec_ofVec {d : ℕ} (x : Vec d) : (ofVec x).toVec = x := sorry

@[simp] theorem ofVec_toVec {d : ℕ} (x : HilbertVec d) : ofVec x.toVec = x := sorry

/-- Algebraic identification between the Euclidean Hilbert carrier and the
project's lightweight vector carrier. -/
def linearEquivVec (d : ℕ) : HilbertVec d ≃ₗ[ℝ] Vec d where
  toFun := toVec
  invFun := ofVec
  left_inv := ofVec_toVec
  right_inv := toVec_ofVec
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Continuous linear identification between the Euclidean Hilbert carrier and
the project's lightweight vector carrier. -/
noncomputable def continuousLinearEquivVec (d : ℕ) : HilbertVec d ≃L[ℝ] Vec d :=
  (linearEquivVec d).toContinuousLinearEquiv

end HilbertVec

/-- The Euclidean Hilbert realization of `d × d` real matrices. The algebraic
carrier `Mat d` keeps its lightweight pointwise role; this wrapper is for
Hilbert-space measurability and `L²` arguments. -/
abbrev HilbertMat (d : ℕ) := PiLp 2 (fun _ : Fin d => HilbertVec d)

namespace HilbertMat

end HilbertMat

/-- The Euclidean Hilbert realization of `\R^{2d}`, viewed as a doubled
potential/flux carrier. -/
abbrev HilbertBlockVec (d : ℕ) := PiLp 2 (fun _ : Fin 2 => HilbertVec d)

namespace HilbertBlockVec

/-- The flux component of a doubled Hilbert vector. -/
abbrev flux {d : ℕ} (X : HilbertBlockVec d) : HilbertVec d :=
  X 1

end HilbertBlockVec

end Homogenization
