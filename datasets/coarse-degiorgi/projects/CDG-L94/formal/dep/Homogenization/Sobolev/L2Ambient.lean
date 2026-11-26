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
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import dep.Homogenization.Ambient.Basic
public import dep.Homogenization.Ambient.BlockMatrix
public import dep.Homogenization.Ambient.HilbertFinite

@[expose] public section

namespace Homogenization

/-- The restricted Lebesgue measure on a domain `U ⊆ \R^d`. -/
noncomputable abbrev volumeMeasureOn {d : ℕ} (U : Set (Vec d)) :=
  MeasureTheory.volume.restrict U

/-- Scalar-valued `L²(U)` with respect to restricted Lebesgue measure. -/
noncomputable abbrev ScalarL2 {d : ℕ} (U : Set (Vec d)) :=
  MeasureTheory.Lp ℝ 2 (volumeMeasureOn U)

/-- Vector-valued `L²(U; \R^d)`. -/
noncomputable abbrev VectorL2 {d : ℕ} (U : Set (Vec d)) :=
  MeasureTheory.Lp (Vec d) 2 (volumeMeasureOn U)

/-- Hilbert-valued `L²(U; \R^d)` built from the custom Euclidean carrier
`HilbertVec d`. This is the intended ambient space for Hilbert-space arguments. -/
noncomputable abbrev HilbertVectorL2 {d : ℕ} (U : Set (Vec d)) :=
  MeasureTheory.Lp (HilbertVec d) 2 (volumeMeasureOn U)

noncomputable instance instMeasurableSpaceHilbertVectorL2 {d : ℕ} {U : Set (Vec d)} :
    MeasurableSpace (HilbertVectorL2 U) :=
  borel _

noncomputable instance instBorelSpaceHilbertVectorL2 {d : ℕ} {U : Set (Vec d)} :
    BorelSpace (HilbertVectorL2 U) := sorry

/-- Predicate-level scalar `L²` membership on `U`. -/
noncomputable abbrev MemScalarL2 {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  MeasureTheory.MemLp u 2 (volumeMeasureOn U)

/-- Predicate-level vector `L²` membership on `U`. -/
noncomputable abbrev MemVectorL2 {d : ℕ} (U : Set (Vec d)) (f : Vec d → Vec d) : Prop :=
  MeasureTheory.MemLp f 2 (volumeMeasureOn U)

/-- Predicate-level Hilbert-vector `L²` membership on `U`. -/
noncomputable abbrev MemHilbertVectorL2 {d : ℕ} (U : Set (Vec d))
    (f : Vec d → HilbertVec d) : Prop :=
  MeasureTheory.MemLp f 2 (volumeMeasureOn U)

/-- Reinterpret a plain vector field as a field valued in the Euclidean Hilbert
carrier. -/
def hilbertifyVecField {d : ℕ} (f : Vec d → Vec d) : Vec d → HilbertVec d :=
  fun x => HilbertVec.ofVec (f x)

/-- Promote a scalar `MemLp` witness to the ambient `ScalarL2` type. -/
noncomputable def toScalarL2 {d : ℕ} {U : Set (Vec d)} {u : Vec d → ℝ}
    (hu : MemScalarL2 U u) : ScalarL2 U :=
  hu.toLp u

/-- Promote a vector `MemLp` witness to the ambient `VectorL2` type. -/
noncomputable def toVectorL2 {d : ℕ} {U : Set (Vec d)} {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) : VectorL2 U :=
  hf.toLp f

/-- Reinterpret a plain vector `L²` witness as a Hilbert-vector `L²` witness. -/
theorem memHilbertVectorL2_hilbertifyVecField {d : ℕ} {U : Set (Vec d)}
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    MemHilbertVectorL2 U (hilbertifyVecField f) := sorry

/-- Promote a Hilbert-vector `MemLp` witness to the ambient `HilbertVectorL2`
type. -/
noncomputable def toHilbertVectorL2 {d : ℕ} {U : Set (Vec d)} {f : Vec d → HilbertVec d}
    (hf : MemHilbertVectorL2 U f) : HilbertVectorL2 U :=
  hf.toLp f

/-- Promote a plain vector `MemLp` witness directly to the Hilbert-vector
ambient type. -/
noncomputable def toHilbertVectorL2OfVecField {d : ℕ} {U : Set (Vec d)} {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) : HilbertVectorL2 U :=
  toHilbertVectorL2 (memHilbertVectorL2_hilbertifyVecField hf)

section CarrierTransport

variable {d : ℕ} {U : Set (Vec d)}

/-- Transport Hilbert-vector `L²` fields back to the plain vector carrier by
applying `HilbertVec -> Vec` pointwise. -/
noncomputable def hilbertVectorL2ToVectorL2 : HilbertVectorL2 U →L[ℝ] VectorL2 U :=
  ((HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap).compLpL 2
    (volumeMeasureOn U)

end CarrierTransport

section ConstantFields

variable {d : ℕ} {U : Set (Vec d)}

variable [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]

end ConstantFields

section Operators

variable {d : ℕ} {U : Set (Vec d)}

variable [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]

end Operators

end Homogenization
