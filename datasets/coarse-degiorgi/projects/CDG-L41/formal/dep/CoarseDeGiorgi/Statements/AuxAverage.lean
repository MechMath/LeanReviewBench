module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Pi
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import dep.CoarseDeGiorgi.Statements.AuxDescendantAverage
public import dep.CoarseDeGiorgi.Statements.AuxDescendantCube
public import dep.CoarseDeGiorgi.Statements.AuxDescendantIndices
public import dep.Homogenization.Ambient.Basic
public import dep.Homogenization.Ambient.CoefficientField
public import dep.Homogenization.Ambient.HilbertFinite
public import dep.Homogenization.Sobolev.L2Ambient

@[expose] public section

open Homogenization MeasureTheory

open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def auxAverage {d : ℕ} (m k : ℤ) (z : Fin d → ℤ)
    (f : Vec d → Vec d) : Vec d → Vec d := by
  classical
  exact fun x => (auxDescendantIndices m k).sum fun n =>
      if x ∈ auxDescendantCube m k z n then auxDescendantAverage m k z n f else 0

end

end CoarseDeGiorgi
