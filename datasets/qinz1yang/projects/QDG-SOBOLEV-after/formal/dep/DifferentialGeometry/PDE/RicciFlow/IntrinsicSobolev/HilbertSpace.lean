import dep.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.Components
import dep.DifferentialGeometry.Integral.Measure.Family
import dep.DifferentialGeometry.Integral.L2.SmoothSections.Defs
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.Completion



noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option warningAsError false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSobolev

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]



private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩




structure SmoothCcTensorHs (g : SmoothRiemannianMetric I M) (r s k : ℕ) where
  
  toCcTensor : SmoothCcTensor g r s

namespace SmoothCcTensorHs

variable {g : SmoothRiemannianMetric I M} {r s k : ℕ}


@[ext] theorem ext {S T : SmoothCcTensorHs g r s k}
    (h : S.toCcTensor = T.toCcTensor) : S = T  := by sorry

lemma toCcTensor_injective :
    Function.Injective
      (fun S : SmoothCcTensorHs g r s k => S.toCcTensor)  := by sorry

instance : Zero (SmoothCcTensorHs g r s k) := ⟨⟨0⟩⟩
instance : Add (SmoothCcTensorHs g r s k) :=
  ⟨fun S T => ⟨S.toCcTensor + T.toCcTensor⟩⟩
instance : Neg (SmoothCcTensorHs g r s k) := ⟨fun S => ⟨-S.toCcTensor⟩⟩
instance : Sub (SmoothCcTensorHs g r s k) :=
  ⟨fun S T => ⟨S.toCcTensor - T.toCcTensor⟩⟩
instance : SMul ℝ (SmoothCcTensorHs g r s k) :=
  ⟨fun c S => ⟨c • S.toCcTensor⟩⟩

@[simp] lemma toCcTensor_zero :
    (0 : SmoothCcTensorHs g r s k).toCcTensor = 0  := by sorry

@[simp] lemma toCcTensor_add (S T : SmoothCcTensorHs g r s k) :
    (S + T).toCcTensor = S.toCcTensor + T.toCcTensor  := by sorry

@[simp] lemma toCcTensor_neg (S : SmoothCcTensorHs g r s k) :
    (-S).toCcTensor = -S.toCcTensor  := by sorry

@[simp] lemma toCcTensor_sub (S T : SmoothCcTensorHs g r s k) :
    (S - T).toCcTensor = S.toCcTensor - T.toCcTensor  := by sorry

@[simp] lemma toCcTensor_smul (c : ℝ) (S : SmoothCcTensorHs g r s k) :
    (c • S).toCcTensor = c • S.toCcTensor  := by sorry

instance : SMul ℕ (SmoothCcTensorHs g r s k) := ⟨nsmulRec⟩
instance : SMul ℤ (SmoothCcTensorHs g r s k) := ⟨zsmulRec⟩

@[simp] lemma toCcTensor_nsmul (S : SmoothCcTensorHs g r s k) (n : ℕ) :
    (n • S).toCcTensor = n • S.toCcTensor  := by sorry

@[simp] lemma toCcTensor_zsmul (S : SmoothCcTensorHs g r s k) (z : ℤ) :
    (z • S).toCcTensor = z • S.toCcTensor  := by sorry

instance : AddCommGroup (SmoothCcTensorHs g r s k) :=
  toCcTensor_injective.addCommGroup
    (fun S => S.toCcTensor)
    toCcTensor_zero
    toCcTensor_add
    toCcTensor_neg
    toCcTensor_sub
    toCcTensor_nsmul
    toCcTensor_zsmul


def toCcTensorAddHom :
    SmoothCcTensorHs g r s k →+ SmoothCcTensor g r s where
  toFun := fun S => S.toCcTensor
  map_zero' := toCcTensor_zero
  map_add' := toCcTensor_add

instance : Module ℝ (SmoothCcTensorHs g r s k) :=
  toCcTensor_injective.module ℝ toCcTensorAddHom toCcTensor_smul

end SmoothCcTensorHs





set_option linter.unusedSectionVars false in

private noncomputable def hkIntegrand
    {g : SmoothRiemannianMetric I M} {r s k : ℕ}
    (T S : SmoothCcTensorHs g r s k) (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) : ℝ :=
  ((chartAtlasPOU I M α : M → ℝ)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
    ((iteratedFDeriv ℝ j
            (tensorChartComponentRaw (I := I) (M := M) g r s
                T.toCcTensor α IJ.1 IJ.2
              ∘ (extChartAt I α).symm
              ∘ (toEuclidean (E := E)).symm) y)
          (fun i => EuclideanSpace.basisFun
            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)) *
      (iteratedFDeriv ℝ j
            (tensorChartComponentRaw (I := I) (M := M) g r s
                S.toCcTensor α IJ.1 IJ.2
              ∘ (extChartAt I α).symm
              ∘ (toEuclidean (E := E)).symm) y)
          (fun i => EuclideanSpace.basisFun
            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)))

set_option linter.unusedSectionVars false in

private noncomputable def hkOneTerm
    {g : SmoothRiemannianMetric I M} {r s k : ℕ}
    (T S : SmoothCcTensorHs g r s k) (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E)) : ℝ :=
  ∫ y in chartTargetEuclid (I := I) (M := M) α,
    hkIntegrand (I := I) (M := M) T S α IJ j basisIdx y
    ∂(volume :
      Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))

set_option linter.unusedSectionVars false in

private noncomputable def hkInner
    {g : SmoothRiemannianMetric I M} {r s k : ℕ}
    (T S : SmoothCcTensorHs g r s k) : ℝ :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ∑ j ∈ Finset.range (2 * k + 1),
        ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
          hkOneTerm (I := I) (M := M) T S α IJ j basisIdx



set_option linter.unusedSectionVars false in

noncomputable instance instPreInnerProductSpaceCore
    {g : SmoothRiemannianMetric I M} {r s k : ℕ} :
    PreInnerProductSpace.Core ℝ (SmoothCcTensorHs g r s k) where
  inner T S := hkInner (I := I) (M := M) T S
  conj_inner_symm T S := by sorry
  re_inner_nonneg T := by sorry
  add_left T₁ T₂ S := by sorry
  smul_left T S c := by sorry

set_option linter.unusedSectionVars false in

noncomputable instance instSeminormedAddCommGroup
    {g : SmoothRiemannianMetric I M} {r s k : ℕ} :
    SeminormedAddCommGroup (SmoothCcTensorHs g r s k) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)

set_option linter.unusedSectionVars false in

noncomputable instance instInnerProductSpace
    {g : SmoothRiemannianMetric I M} {r s k : ℕ} :
    InnerProductSpace ℝ (SmoothCcTensorHs g r s k) :=
  InnerProductSpace.ofCore _




abbrev TensorPouSobolevHilbert
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) : Type _ :=
  UniformSpace.Completion (SmoothCcTensorHs g r s k)



namespace SmoothCcTensor


noncomputable def toHs {g : SmoothRiemannianMetric I M} {r s : ℕ} (k : ℕ)
    (T : SmoothCcTensor g r s) :
    TensorPouSobolevHilbert (I := I) (M := M) g r s k :=
  ((⟨T⟩ : SmoothCcTensorHs g r s k) : TensorPouSobolevHilbert g r s k)

end SmoothCcTensor



namespace Preservation
noncomputable def hkIntegrandValue := @hkIntegrand
noncomputable def hkOneTermValue := @hkOneTerm
noncomputable def hkInnerValue := @hkInner
end Preservation

end IntrinsicSobolev
end RicciFlow
end PDE
end DifferentialGeometry

end
