module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import dep.Homogenization.Ambient.Basic
public import dep.Homogenization.Ambient.HilbertFinite
public import dep.Homogenization.Sobolev.L2Ambient

@[expose] public section

namespace Homogenization

abbrev CoeffField (d : ℕ) := Vec d → Mat d

def IsEllipticMatrix {d : ℕ} (lam Lam : ℝ) (A : Mat d) : Prop :=
  0 < lam ∧
    lam ≤ Lam ∧
    (∀ ξ : Vec d, lam * vecNormSq ξ ≤ vecDot ξ (matVecMul A ξ)) ∧
    (∀ ξ : Vec d, Lam⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul A⁻¹ ξ))

namespace IsEllipticMatrix

end IsEllipticMatrix

def IsEllipticFieldOn {d : ℕ} (lam Lam : ℝ) (U : Set (Vec d)) (a : CoeffField d) : Prop :=
  by
    classical
    exact
      Measurable (fun x i j => if x ∈ U then a x i j else 0) ∧
        ∀ x ∈ U, IsEllipticMatrix lam Lam (a x)

namespace IsEllipticFieldOn

end IsEllipticFieldOn

noncomputable def restrictCoeffField {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) : CoeffField d := by
  classical
  exact fun x => if x ∈ U then a x else 0

end Homogenization
