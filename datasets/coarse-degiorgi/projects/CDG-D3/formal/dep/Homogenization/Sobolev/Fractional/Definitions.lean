module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Bounded
public import dep.Homogenization.Ambient.Basic
public import dep.Homogenization.Geometry.Domain
public import dep.Homogenization.Geometry.TriadicCube
public import dep.Homogenization.Multiscale.NormalizedNorms

@[expose] public section

namespace Homogenization

namespace Gagliardo

noncomputable section

open MeasureTheory

open scoped ENNReal

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The kernel exponent `s + d/p`.  At `p = ∞` it collapses to `s`. -/
def kernelExponent (d : ℕ) (s : ℝ) (p : ℝ≥0∞) : ℝ :=
  s + (d : ℝ) / p.toReal

/-- Difference-quotient kernel of the fractional Sobolev seminorm. -/
noncomputable def gagliardoKernel (s : ℝ) (p : ℝ≥0∞) (u : Vec d → E) :
    Vec d × Vec d → E :=
  fun z => (dist z.1 z.2 ^ (-kernelExponent d s p)) • (u z.1 - u z.2)

/-- The manuscript's `⨍_□ ∫_□` normalization as a product measure:
normalized in the first variable, plain restricted volume in the second. -/
noncomputable def gagliardoCubeMeasure (Q : TriadicCube d) :
    Measure (Vec d × Vec d) :=
  (normalizedCubeMeasure Q).prod (cubeMeasure Q)

instance instIsFiniteMeasureGagliardoCubeMeasure (Q : TriadicCube d) :
    IsFiniteMeasure (gagliardoCubeMeasure Q) := sorry

instance instSFiniteGagliardoCubeMeasure (Q : TriadicCube d) :
    SFinite (gagliardoCubeMeasure Q) := sorry

/-- `u ∈ W^{s,p}(Q)`: the membership predicate, mirroring `MemLp`. -/
def MemWsp (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → E) : Prop :=
  MemLp (gagliardoKernel s p u) p (gagliardoCubeMeasure Q)

namespace Internal

end Internal

theorem MemWsp.add {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞} {u v : Vec d → E}
    (hu : MemWsp Q s p u) (hv : MemWsp Q s p v) :
    MemWsp Q s p (u + v) := sorry

theorem MemWsp.neg {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞} {u : Vec d → E}
    (hu : MemWsp Q s p u) :
    MemWsp Q s p (-u) := sorry

theorem MemWsp.smul {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞} {u : Vec d → E}
    (c : ℝ) (hu : MemWsp Q s p u) :
    MemWsp Q s p (c • u) := sorry

end

end Gagliardo

end Homogenization
