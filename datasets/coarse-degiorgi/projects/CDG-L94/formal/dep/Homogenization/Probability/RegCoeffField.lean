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
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Support
public import dep.Homogenization.Ambient.Basic
public import dep.Homogenization.Ambient.BlockMatrix
public import dep.Homogenization.Ambient.CoefficientField
public import dep.Homogenization.Ambient.HilbertFinite
public import dep.Homogenization.Sobolev.L2Ambient

@[expose] public section

namespace Homogenization

open MeasureTheory

noncomputable section

/-- The regular-fields carrier: entrywise-Borel-measurable, locally-integrable
coefficient fields.  Regularity is now free by type: every element carries a
proof that each of its scalar entries is measurable and locally integrable
(the paper, Armstrong–Kuusi–Loher, to appear). -/
structure RegCoeffField (d : ℕ) where
  /-- The underlying raw coefficient field. -/
  toFun : Vec d → Mat d
  /-- Each scalar entry is Borel measurable. -/
  entry_measurable : ∀ i j, Measurable (fun x : Vec d => toFun x i j)
  /-- Each scalar entry is locally integrable for the Lebesgue measure. -/
  entry_locInt : ∀ i j, LocallyIntegrable (fun x : Vec d => toFun x i j) volume

namespace RegCoeffField

variable {d : ℕ}

instance : CoeFun (RegCoeffField d) (fun _ => Vec d → Mat d) := ⟨toFun⟩

/-- Coercion back to the raw deterministic carrier `CoeffField d`.  Deterministic
layers receive `a.toCoeffField = a.toFun` and are untouched by the carrier. -/
def toCoeffField (a : RegCoeffField d) : CoeffField d := a.toFun

instance : Zero (RegCoeffField d) where
  zero :=
    { toFun := 0
      entry_measurable := fun i j => sorry
      entry_locInt := fun i j => sorry }

instance : Add (RegCoeffField d) where
  add a b :=
    { toFun := a.toFun + b.toFun
      entry_measurable := fun i j =>
        (a.entry_measurable i j).add (b.entry_measurable i j)
      entry_locInt := fun i j => (a.entry_locInt i j).add (b.entry_locInt i j) }

instance : SMul ℝ (RegCoeffField d) where
  smul c a :=
    { toFun := fun x => c • a x
      entry_measurable := fun i j => sorry
      entry_locInt := fun i j => sorry }

instance : AddCommMonoid (RegCoeffField d) where
  add_assoc a b c := sorry
  zero_add a := sorry
  add_zero a := sorry
  add_comm a b := sorry
  nsmul := nsmulRec

/-- The constant regular field with value the matrix `M`.  Constant maps are
measurable and locally integrable, so this is a genuine carrier element. -/
def constRegCoeffField (M : Mat d) : RegCoeffField d where
  toFun := fun _ => M
  entry_measurable := fun _ _ => measurable_const
  entry_locInt := fun i j => MeasureTheory.locallyIntegrable_const (M i j)

/-- The constant identity-matrix field. -/
instance : One (RegCoeffField d) := ⟨constRegCoeffField 1⟩

end RegCoeffField

end

end Homogenization
