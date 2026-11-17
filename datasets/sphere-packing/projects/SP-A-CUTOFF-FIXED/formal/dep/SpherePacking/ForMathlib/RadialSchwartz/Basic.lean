module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

@[expose] public section

namespace Function

variable {D E F : Type*}

/-- A function on a space with a norm is *radial* if factors through the norm. -/
def IsRadial [Norm E] (f : E → F) : Prop := f.FactorsThrough (‖·‖ : E → ℝ)

namespace IsRadial

lemma comp_right [Norm D] {f : D → E} {g : E → F} (hf : f.IsRadial) :
  (g ∘ f).IsRadial := sorry

end IsRadial

section Norm

open IsRadial

variable [Norm E]

variable (E) in
lemma isRadial_norm_sq : IsRadial (‖·‖ ^ 2 : E → ℝ) := sorry

end Norm

section Isometries

end Isometries

end Function

section RadialSchwartz

open Function SchwartzMap

/-- The submodule of radial Schwartz functions inside the Schwartz space `𝓢(E, F)`. -/
@[simps]
def RadialSchwartzMap (𝕜 E F : Type*) [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] :
    Submodule 𝕜 𝓢(E, F) where
  carrier := {f | IsRadial f}
  add_mem' := sorry
  zero_mem' := sorry
  smul_mem' := sorry

namespace RadialSchwartzMap

variable {𝕜 E F : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- Create a `RadialSchwartzMap` -/
def mk [NormedSpace ℝ E] (f : 𝓢(E, F)) (hf : IsRadial f) : RadialSchwartzMap 𝕜 E F := ⟨f, hf⟩

section NormedSpace

variable [NormedSpace ℝ E]

instance instFunLike : FunLike (RadialSchwartzMap 𝕜 E F) E F where
  coe f := f.1
  coe_injective := DFunLike.coe_injective.comp Subtype.val_injective

end NormedSpace

end RadialSchwartzMap

noncomputable section Fourier

open Real FourierTransform

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace 𝕜 F] [SMulCommClass ℂ 𝕜 F]

/-- The Fourier transform of a radial function is radial. -/
lemma Function.IsRadial.fourier {f : E → F} (hf : f.IsRadial) : (𝓕 f).IsRadial := sorry

variable (𝕜) in
lemma SchwartzMap.fourier_mem_radialSchwartzMap_of_mem_radialSchwartzMap {f : 𝓢(E, F)}
    (hf : f ∈ RadialSchwartzMap 𝕜 E F) : 𝓕 f ∈ RadialSchwartzMap 𝕜 E F := sorry

namespace RadialSchwartzMap

variable (𝕜 E F)

/-- The Fourier transform as a continuous linear map on radial Schwartz functions. -/
def fourierTransformCLM : RadialSchwartzMap 𝕜 E F →L[𝕜] RadialSchwartzMap 𝕜 E F :=
  (SchwartzMap.fourierTransformCLM 𝕜).restrict fun _ ↦
    fourier_mem_radialSchwartzMap_of_mem_radialSchwartzMap 𝕜

instance instFourierTransform :
    FourierTransform (RadialSchwartzMap 𝕜 E F) (RadialSchwartzMap 𝕜 E F) where
  fourier := fourierTransformCLM 𝕜 E F

variable {𝕜 E F}

section inverse

lemma _root_.Function.Even.fourierInv {f : E → F} (hf : (𝓕 f).Even) {w : E} :
    𝓕⁻ f w = 𝓕 f w := sorry

instance instFourierInv :
    FourierTransformInv (RadialSchwartzMap 𝕜 E F) (RadialSchwartzMap 𝕜 E F) where
  fourierInv := fourierTransformCLM 𝕜 E F

variable [CompleteSpace F]

instance instFourierPair : FourierPair (RadialSchwartzMap 𝕜 E F) (RadialSchwartzMap 𝕜 E F) := sorry

variable {f : RadialSchwartzMap 𝕜 E F}

/-- The Fourier transform is an involution on radial Schwartz functions. -/
@[simp]
lemma fourier_apply_apply : 𝓕 (𝓕 f) = f := sorry

instance instFourierInvPair :
    FourierInvPair (RadialSchwartzMap 𝕜 E F) (RadialSchwartzMap 𝕜 E F) := sorry

end inverse

section MoreFourierInstances

instance instFourierAdd : FourierAdd (RadialSchwartzMap 𝕜 E F) (RadialSchwartzMap 𝕜 E F) := sorry

instance instFourierInvAdd : FourierInvAdd (RadialSchwartzMap 𝕜 E F) (RadialSchwartzMap 𝕜 E F) := sorry

instance instFourierSMul : FourierSMul 𝕜 (RadialSchwartzMap 𝕜 E F) (RadialSchwartzMap 𝕜 E F) := sorry

instance instFourierInvSMul :
    FourierInvSMul 𝕜 (RadialSchwartzMap 𝕜 E F) (RadialSchwartzMap 𝕜 E F) := sorry

instance instContinuousFourier :
    ContinuousFourier (RadialSchwartzMap 𝕜 E F) (RadialSchwartzMap 𝕜 E F) := sorry

instance instContinuousFourierInv :
    ContinuousFourierInv (RadialSchwartzMap 𝕜 E F) (RadialSchwartzMap 𝕜 E F) := sorry

end MoreFourierInstances

end RadialSchwartzMap

end Fourier

noncomputable section Star

open FourierTransform

namespace RadialSchwartzMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace 𝕜 F] [SMulCommClass ℂ 𝕜 F]

variable [CompleteSpace F]

instance instStarAddMonoid : StarAddMonoid (RadialSchwartzMap 𝕜 E F) where
  star := 𝓕
  star_involutive := fun _ ↦ fourier_apply_apply
  star_add := instFourierAdd.fourier_add

instance instStarModule : StarModule ℝ (RadialSchwartzMap 𝕜 E F) := sorry

variable {f : RadialSchwartzMap 𝕜 E F}

end RadialSchwartzMap

end Star

end RadialSchwartz
