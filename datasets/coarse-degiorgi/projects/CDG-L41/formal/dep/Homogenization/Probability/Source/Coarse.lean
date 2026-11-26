module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Support
public import dep.Homogenization.Ambient.Basic
public import dep.Homogenization.Ambient.CoefficientField
public import dep.Homogenization.Ambient.Euclidean
public import dep.Homogenization.Ambient.HilbertFinite
public import dep.Homogenization.Geometry.SignedPermutation
public import dep.Homogenization.Sobolev.L2Ambient

@[expose] public section

namespace Homogenization.Source.Coarse

open MeasureTheory

def euclideanBall {d : ℕ} (R : ℝ) : Set (Vec d) :=
  {x | euclideanNorm x < R}

structure SmoothCompactProbe {d : ℕ} (φ : Vec d → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) φ
  compact : HasCompactSupport φ

def Carrier (d : ℕ) :=
  {a : CoeffField d //
    (∀ i j, Measurable (fun x : Vec d => a x i j)) ∧
    ∀ R : ℝ, 1 ≤ R → ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ x, x ∈ euclideanBall R → IsEllipticMatrix ε ε⁻¹ (a x)}

instance instCoeFunCarrier (d : ℕ) : CoeFun (Carrier d) (fun _ => CoeffField d) where
  coe a := a.1

noncomputable def bilinearTest {d : ℕ} (e e' : Vec d)
    (φ : Vec d → ℝ) (a : Carrier d) : ℝ :=
  ∫ x, vecDot e' (matVecMul (a x) e) * φ x ∂volume

set_option warn.classDefReducibility false in
def localSigma {d : ℕ} (U : Set (Vec d)) (_hU : MeasurableSet U) :
    MeasurableSpace (Carrier d) :=
  MeasurableSpace.generateFrom
    {s | ∃ (e e' : Vec d) (φ : Vec d → ℝ),
      SmoothCompactProbe φ ∧ tsupport φ ⊆ U ∧
      ∃ t : Set ℝ, MeasurableSet t ∧ s = bilinearTest e e' φ ⁻¹' t}

set_option warn.classDefReducibility false in
def globalSigma (d : ℕ) : MeasurableSpace (Carrier d) :=
  localSigma Set.univ MeasurableSet.univ

instance instMeasurableSpaceCarrier (d : ℕ) : MeasurableSpace (Carrier d) :=
  globalSigma d

end Homogenization.Source.Coarse
