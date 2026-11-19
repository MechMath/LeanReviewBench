


import dep.DifferentialGeometry.Tensor.Multilinear.Bundle.Fiber
import dep.DifferentialGeometry.Tensor.Multilinear.Bundle.Section
import dep.DifferentialGeometry.Tensor.Product.Basis
import dep.DifferentialGeometry.Tensor.Product.Bundle
import dep.DifferentialGeometry.Bundle.Section
import Mathlib.RingTheory.TensorProduct.Finite
open DifferentialGeometry.Tensor.Multilinear

noncomputable section


open Bundle Set

open scoped Manifold Topology Bundle ContDiff BigOperators TensorProduct

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

noncomputable def productFun {s q : ℕ} {x : B}
    (α : Bundle.continuousMultilinearMap 𝕜 s F E x)
    (β : Bundle.continuousMultilinearMap 𝕜 q F E x) :
    Bundle.continuousMultilinearMap 𝕜 (s + q) F E x :=
  ofModel (F := F) (E := E)
    ((toModel (F := F) (E := E) α |>.smulRight
      (toModel (F := F) (E := E) β)).uncurrySum.domDomCongr finSumFinEquiv)

scoped infixl:70 " ⊗ₘ " => productFun

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
theorem product_fun_apply {s q : ℕ} {x : B}
    (α : Bundle.continuousMultilinearMap 𝕜 s F E x)
    (β : Bundle.continuousMultilinearMap 𝕜 q F E x)
    (v : Fin (s + q) → E x) :
    productFun α β v = α (v ∘ Fin.castAdd q) * β (v ∘ Fin.natAdd s)  := by sorry

theorem triv_coord_product {s q d : ℕ}
    (b : Module.Basis (Fin d) 𝕜 F)
    (σ : Fin (s + q) → Fin d) (x₀ x : B)
    (α : Bundle.continuousMultilinearMap 𝕜 s F E x)
    (β : Bundle.continuousMultilinearMap 𝕜 q F E x) :
    (continuousMultilinearMapBasis b (s + q)).repr
      (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin (s + q) => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) x₀
        ⟨x, productFun α β⟩).2 σ =
    (continuousMultilinearMapBasis b s).repr
      (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x) x₀ ⟨x, α⟩).2
        (σ ∘ Fin.castAdd q) *
    (continuousMultilinearMapBasis b q).repr
      (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 q F E x) x₀ ⟨x, β⟩).2
        (σ ∘ Fin.natAdd s)  := by sorry

noncomputable def productBilinear (s q : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 s F E x →ₗ[𝕜]
    Bundle.continuousMultilinearMap 𝕜 q F E x →ₗ[𝕜]
    Bundle.continuousMultilinearMap 𝕜 (s + q) F E x :=
  LinearMap.mk₂ 𝕜 productFun
    (fun α₁ α₂ β => by
      apply toModel_injective (F := F) (E := E)
      simp only [productFun, toModel_add, toModel_ofModel]
      ext m
      simp only [ContinuousMultilinearMap.domDomCongr_apply,
                 ContinuousMultilinearMap.uncurrySum_apply,
                 ContinuousMultilinearMap.smulRight_apply,
                 add_apply,
                 smul_apply, smul_eq_mul]
      ring)
    (fun c α β => by
      apply toModel_injective (F := F) (E := E)
      simp only [productFun, toModel_smul, toModel_ofModel]
      ext m
      simp only [ContinuousMultilinearMap.domDomCongr_apply,
                 ContinuousMultilinearMap.uncurrySum_apply,
                 ContinuousMultilinearMap.smulRight_apply,
                 smul_apply, smul_eq_mul]
      ring)
    (fun α β₁ β₂ => by
      apply toModel_injective (F := F) (E := E)
      simp only [productFun, toModel_add, toModel_ofModel]
      ext m
      simp only [ContinuousMultilinearMap.domDomCongr_apply,
                 ContinuousMultilinearMap.uncurrySum_apply,
                 ContinuousMultilinearMap.smulRight_apply,
                 add_apply,
                 smul_apply, smul_eq_mul]
      ring)
    (fun c α β => by
      apply toModel_injective (F := F) (E := E)
      simp only [productFun, toModel_smul, toModel_ofModel]
      ext m
      simp only [ContinuousMultilinearMap.domDomCongr_apply,
                 ContinuousMultilinearMap.uncurrySum_apply,
                 ContinuousMultilinearMap.smulRight_apply,
                 smul_apply, smul_eq_mul]
      ring)

noncomputable def fromTensor (s q : ℕ) (x : B) :
    TensorProduct 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (Bundle.continuousMultilinearMap 𝕜 q F E x) →ₗ[𝕜]
    Bundle.continuousMultilinearMap 𝕜 (s + q) F E x :=
  TensorProduct.lift (productBilinear (F := F) (E := E) s q x)

noncomputable def modelProduct (s q : ℕ)
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (g : ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (s + q) => F) 𝕜 :=
  (f.smulRight g).uncurrySum.domDomCongr finSumFinEquiv

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
theorem modelProduct_apply (s q : ℕ)
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (g : ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
    (v : Fin (s + q) → F) :
    modelProduct s q f g v = f (v ∘ Fin.castAdd q) * g (v ∘ Fin.natAdd s)  := by sorry

noncomputable def modelFromTensor (s q : ℕ) :
    TensorProduct 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜) →ₗ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (s + q) => F) 𝕜 :=
  TensorProduct.lift (LinearMap.mk₂ 𝕜 (modelProduct (𝕜 := 𝕜) (F := F) s q)
    (fun f₁ f₂ g => by ext v; simp [modelProduct_apply, add_mul])
    (fun c f g => by ext v; simp [modelProduct_apply]; ring)
    (fun f g₁ g₂ => by ext v; simp [modelProduct_apply, mul_add])
    (fun c f g => by ext v; simp [modelProduct_apply]; ring))

theorem modelFromTensor_basisElem {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F)
    (s q : ℕ) (σ : Fin (s + q) → Fin d) :
    modelFromTensor (𝕜 := 𝕜) (F := F) s q
      (continuousMultilinearMapBasisElem b s (σ ∘ Fin.castAdd q) ⊗ₜ[𝕜]
       continuousMultilinearMapBasisElem b q (σ ∘ Fin.natAdd s)) =
    continuousMultilinearMapBasisElem b (s + q) σ  := by sorry

theorem modelFromTensor_surjective {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F)
    (s q : ℕ) :
    Function.Surjective (modelFromTensor (𝕜 := 𝕜) (F := F) s q)  := by sorry

noncomputable def modelFromTensorEquiv {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F)
    (s q : ℕ) :
    TensorProduct 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜) ≃ₗ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (s + q) => F) 𝕜 := by
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional s
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional q
  haveI : FiniteDimensional 𝕜 (TensorProduct 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)) :=
    Module.Finite.tensorProduct 𝕜 _ _
  exact LinearEquiv.ofBijective (modelFromTensor s q)
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
        rw [Module.finrank_tensorProduct,
          finrank_continuousMultilinearMap s,
          finrank_continuousMultilinearMap q,
          finrank_continuousMultilinearMap (s + q), pow_add])).mpr
      (modelFromTensor_surjective b s q),
     modelFromTensor_surjective b s q⟩

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
theorem product_fun_ofModel {s q : ℕ} {x : B}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (g : ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜) :
    productFun (ofModel (F := F) (E := E) (x := x) f)
                (ofModel (F := F) (E := E) (x := x) g) =
    ofModel (modelProduct s q f g)  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
theorem fromTensor_map_ofModel {s q : ℕ} {x : B}
    (t : TensorProduct 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)) :
    fromTensor s q x (TensorProduct.map
      ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) s x).symm :
        ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 →ₗ[𝕜]
        Bundle.continuousMultilinearMap 𝕜 s F E x)
      ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) q x).symm :
        ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜 →ₗ[𝕜]
        Bundle.continuousMultilinearMap 𝕜 q F E x) t) =
    ofModel (F := F) (E := E) (x := x) (modelFromTensor s q t)  := by sorry

noncomputable def equiv (s q : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 (s + q) F E x ≃ₗ[𝕜]
    TensorProduct 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (Bundle.continuousMultilinearMap 𝕜 q F E x) := by
  haveI := instFiniteDimensional (𝕜 := 𝕜) (F := F) (E := E) s x
  haveI := instFiniteDimensional (𝕜 := 𝕜) (F := F) (E := E) q x
  haveI := instFiniteDimensional (𝕜 := 𝕜) (F := F) (E := E) (s + q) x
  haveI : Module.Free 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) :=
    Module.Free.of_divisionRing 𝕜 _
  haveI : Module.Free 𝕜 (Bundle.continuousMultilinearMap 𝕜 q F E x) :=
    Module.Free.of_divisionRing 𝕜 _
  haveI : Module.Free 𝕜 (Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) :=
    Module.Free.of_divisionRing 𝕜 _
  haveI : FiniteDimensional 𝕜 (TensorProduct 𝕜
      (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (Bundle.continuousMultilinearMap 𝕜 q F E x)) :=
    Module.Finite.tensorProduct 𝕜 _ _
  exact LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_tensorProduct,
        finrank_eq (𝕜 := 𝕜) (F := F) (E := E) s x,
        finrank_eq (𝕜 := 𝕜) (F := F) (E := E) q x,
        finrank_eq (𝕜 := 𝕜) (F := F) (E := E) (s + q) x, pow_add])

end Bundle.continuousMultilinearMap

end

noncomputable section


open Bundle Set ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators TensorProduct

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

local notation "MLF" s => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

namespace Bundle.continuousMultilinearMap

theorem triv_fromTensor_eq_modelFromTensor (s q : ℕ) (x₀ x : B)
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (t : Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
         Bundle.continuousMultilinearMap 𝕜 q F E x) :
    letI := Bundle.TensorProduct.tensorFiberTopology
      𝕜 (MLF s) (MLF q)
      (Bundle.continuousMultilinearMap 𝕜 s F E)
      (Bundle.continuousMultilinearMap 𝕜 q F E)
    letI := Bundle.TensorProduct.fiberBundle
      (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
      (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
      (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
    (trivializationAt (MLF (s + q))
      (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) x₀
      ⟨x, fromTensor s q x t⟩).2 =
    modelFromTensor (𝕜 := 𝕜) (F := F) s q
      ((trivializationAt ((MLF s) ⊗[𝕜] (MLF q))
        (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                   Bundle.continuousMultilinearMap 𝕜 q F E x) x₀
        ⟨x, t⟩).2)  := by sorry

theorem triv_toTensor_eq_modelFromTensorEquiv_symm {d : ℕ}
    (b : Module.Basis (Fin d) 𝕜 F) (s q : ℕ) (x₀ x : B)
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (t : Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
         Bundle.continuousMultilinearMap 𝕜 q F E x) :
    letI := Bundle.TensorProduct.tensorFiberTopology
      𝕜 (MLF s) (MLF q)
      (Bundle.continuousMultilinearMap 𝕜 s F E)
      (Bundle.continuousMultilinearMap 𝕜 q F E)
    letI := Bundle.TensorProduct.fiberBundle
      (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
      (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
      (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
    (modelFromTensorEquiv (𝕜 := 𝕜) (F := F) b s q).symm
      ((trivializationAt (MLF (s + q))
        (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) x₀
        ⟨x, fromTensor s q x t⟩).2) =
    (trivializationAt ((MLF s) ⊗[𝕜] (MLF q))
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 q F E x) x₀
      ⟨x, t⟩).2  := by sorry

end Bundle.continuousMultilinearMap

namespace DifferentialGeometry.MultilinearSection

variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

section Product

variable {s q : ℕ}

noncomputable def product
    (α : MultilinearSection 𝕜 F IB E n s)
    (β : MultilinearSection 𝕜 F IB E n q) :
    MultilinearSection 𝕜 F IB E n (s + q) :=
  ⟨fun x => (α x).productFun (β x), by
    let d := Module.finrank 𝕜 F
    let b : Module.Basis (Fin d) 𝕜 F := Module.finBasis 𝕜 F
    rw [contMDiff_multilinearSection_iff_coord E n b]
    intro σ x₀
    have hα := ((contMDiff_multilinearSection_iff_coord E n b
      (fun x => (α x : Bundle.continuousMultilinearMap 𝕜 s F E x))).mp α.contMDiff)
    have hβ := ((contMDiff_multilinearSection_iff_coord E n b
      (fun x => (β x : Bundle.continuousMultilinearMap 𝕜 q F E x))).mp β.contMDiff)
    simp_rw [Bundle.continuousMultilinearMap.triv_coord_product b σ x₀ _ (α _) (β _)]
    exact (contMDiffAt_const (c := ContinuousLinearMap.mul 𝕜 𝕜).clm_apply
      (hα (σ ∘ Fin.castAdd q) x₀)).clm_apply (hβ (σ ∘ Fin.natAdd s) x₀)⟩

@[simp] theorem product_zero (α : MultilinearSection 𝕜 F IB E n s) :
    product (IB := IB) n α (0 : MultilinearSection 𝕜 F IB E n q)
      = (0 : MultilinearSection 𝕜 F IB E n (s + q))  := by sorry

theorem product_add_left (α β : MultilinearSection 𝕜 F IB E n s)
    (γ : MultilinearSection 𝕜 F IB E n q) :
    product (IB := IB) n (α + β) γ
      = product (IB := IB) n α γ + product (IB := IB) n β γ  := by sorry

end Product

section TensorProductInstances

variable {s q : ℕ}

local instance multilinearTensorFiberTopology {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜]
    {B : Type*} [TopologicalSpace B] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] (s q : ℕ) :
    ∀ x : B, TopologicalSpace (Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                                Bundle.continuousMultilinearMap 𝕜 q F E x) :=
  Bundle.TensorProduct.tensorFiberTopology 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
    (Bundle.continuousMultilinearMap 𝕜 s F E)
    (Bundle.continuousMultilinearMap 𝕜 q F E)

local instance multilinearTensorFiberBundle {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜]
    {B : Type*} [TopologicalSpace B] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] (s q : ℕ) :
    FiberBundle
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 ⊗[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 q F E x) :=
  Bundle.TensorProduct.fiberBundle (𝕜 := 𝕜)
    (F₁ := ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (F₂ := ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
    (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
    (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)

local instance multilinearTensorVectorBundle {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜]
    {B : Type*} [TopologicalSpace B] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] (s q : ℕ) :
    VectorBundle 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 ⊗[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 q F E x) :=
  Bundle.TensorProduct.vectorBundle (𝕜 := 𝕜)
    (F₁ := ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (F₂ := ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
    (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
    (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)

section BundleEquiv

open Bundle.continuousMultilinearMap

noncomputable def multilinearTensorFiberwiseEquiv (s q : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 (s + q) F E x ≃ₗ[𝕜]
    TensorProduct 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (Bundle.continuousMultilinearMap 𝕜 q F E x) :=
  (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) (s + q) x).toLinearEquiv.trans
    ((modelFromTensorEquiv (Module.finBasis 𝕜 F) s q).symm.trans
      (TensorProduct.congr
        (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) s x).symm.toLinearEquiv
        (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) q x).symm.toLinearEquiv))

theorem multilinearTensorFiberwiseEquiv_symm_eq (s q : ℕ) (x : B)
    (t : TensorProduct 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (Bundle.continuousMultilinearMap 𝕜 q F E x)) :
    (multilinearTensorFiberwiseEquiv s q x).symm t = fromTensor s q x t  := by sorry

noncomputable def modelFromTensorCLM (s q : ℕ) :
    ((MLF s) ⊗[𝕜] (MLF q)) →L[𝕜] (MLF (s + q)) :=
  haveI := continuousMultilinearMap_finiteDimensional (𝕜 := 𝕜) (F := F) s
  haveI := continuousMultilinearMap_finiteDimensional (𝕜 := 𝕜) (F := F) q
  haveI : FiniteDimensional 𝕜 ((MLF s) ⊗[𝕜] (MLF q)) :=
    Module.Finite.tensorProduct 𝕜 _ _
  (modelFromTensor (𝕜 := 𝕜) (F := F) s q).toContinuousLinearMap

noncomputable def modelToTensorCLM (s q : ℕ) :
    (MLF (s + q)) →L[𝕜] ((MLF s) ⊗[𝕜] (MLF q)) :=
  haveI := continuousMultilinearMap_finiteDimensional (𝕜 := 𝕜) (F := F) s
  haveI := continuousMultilinearMap_finiteDimensional (𝕜 := 𝕜) (F := F) q
  haveI : FiniteDimensional 𝕜 ((MLF s) ⊗[𝕜] (MLF q)) :=
    Module.Finite.tensorProduct 𝕜 _ _
  haveI := continuousMultilinearMap_finiteDimensional (𝕜 := 𝕜) (F := F) (s + q)
  LinearMap.toContinuousLinearMap
    (modelFromTensorEquiv (𝕜 := 𝕜) (F := F) (Module.finBasis 𝕜 F) s q).symm.toLinearMap

theorem trivializationAt_multilinearTensorFiberwiseEquiv_eq (s q : ℕ) (x₀ x : B)
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (α : Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) :
    (trivializationAt ((MLF s) ⊗[𝕜] (MLF q))
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 q F E x) x₀
      ⟨x, multilinearTensorFiberwiseEquiv s q x α⟩).2 =
    modelToTensorCLM s q
      ((trivializationAt (MLF (s + q))
        (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) x₀
        ⟨x, α⟩).2)  := by sorry

omit [ContMDiffVectorBundle n F E IB] in
theorem multilinearTensorFiberwiseEquiv_smooth
    (_hE : ContMDiffVectorBundle n F E IB) :
    ContMDiff
      (IB.prod 𝓘(𝕜, MLF (s + q)))
      (IB.prod 𝓘(𝕜, (MLF s) ⊗[𝕜] (MLF q)))
      n
      (fun p : TotalSpace (MLF (s + q))
          (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) =>
        (⟨p.1, multilinearTensorFiberwiseEquiv s q p.1 p.2⟩ :
          TotalSpace ((MLF s) ⊗[𝕜] (MLF q))
            (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                       Bundle.continuousMultilinearMap 𝕜 q F E x)))  := by sorry

omit [ContMDiffVectorBundle n F E IB] in
theorem multilinearTensorFiberwiseEquiv_symm_smooth
    (_hE : ContMDiffVectorBundle n F E IB) :
    ContMDiff
      (IB.prod 𝓘(𝕜, (MLF s) ⊗[𝕜] (MLF q)))
      (IB.prod 𝓘(𝕜, MLF (s + q)))
      n
      (fun p : TotalSpace ((MLF s) ⊗[𝕜] (MLF q))
          (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                     Bundle.continuousMultilinearMap 𝕜 q F E x) =>
        (⟨p.1, (multilinearTensorFiberwiseEquiv s q p.1).symm p.2⟩ :
          TotalSpace (MLF (s + q))
            (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x)))  := by sorry

noncomputable def multilinearBundleTensorProductEquiv :
    ContMDiffVectorBundleEquiv 𝕜 IB n
      (MLF (s + q))
      (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x)
      ((MLF s) ⊗[𝕜] (MLF q))
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 q F E x) :=
  ContMDiffVectorBundleEquiv.ofFiberwiseLinearEquiv
    (fun x => multilinearTensorFiberwiseEquiv s q x)
    (multilinearTensorFiberwiseEquiv_smooth n inferInstance)
    (multilinearTensorFiberwiseEquiv_symm_smooth n inferInstance)

noncomputable def toTensorProduct
    (α : MultilinearSection 𝕜 F IB E n (s + q)) :
    ContMDiffSection IB ((MLF s) ⊗[𝕜] (MLF q)) n
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 q F E x) :=
  ⟨fun x => multilinearTensorFiberwiseEquiv s q x (α x),
   ((multilinearTensorFiberwiseEquiv_smooth n inferInstance).comp α.contMDiff).congr fun _ => rfl⟩

noncomputable def fromTensorProduct
    (γ : ContMDiffSection IB ((MLF s) ⊗[𝕜] (MLF q)) n
            (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                       Bundle.continuousMultilinearMap 𝕜 q F E x)) :
    MultilinearSection 𝕜 F IB E n (s + q) :=
  ⟨fun x => (multilinearTensorFiberwiseEquiv s q x).symm (γ x),
   ((multilinearTensorFiberwiseEquiv_symm_smooth n inferInstance).comp γ.contMDiff).congr fun _
     => rfl⟩

theorem fromTensorProduct_toTensorProduct
    (α : MultilinearSection 𝕜 F IB E n (s + q)) (x : B) :
    (fromTensorProduct n (toTensorProduct n α)).1 x = α x  := by sorry

theorem toTensorProduct_fromTensorProduct
    (γ : ContMDiffSection IB ((MLF s) ⊗[𝕜] (MLF q)) n
            (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                       Bundle.continuousMultilinearMap 𝕜 q F E x))
    (x : B) :
    (toTensorProduct n (fromTensorProduct n γ)).1 x = γ x  := by sorry

theorem toTensorProduct_add
    (α β : MultilinearSection 𝕜 F IB E n (s + q)) (x : B) :
    (toTensorProduct n (α + β)).1 x =
    (toTensorProduct n α).1 x + (toTensorProduct n β).1 x  := by sorry

theorem toTensorProduct_smulByFun
    (φ : B → 𝕜) (hφ : ContMDiff IB 𝓘(𝕜) n φ)
    (α : MultilinearSection 𝕜 F IB E n (s + q)) (x : B) :
    (toTensorProduct n (smulByFun n φ hφ α)).1 x =
    φ x • (toTensorProduct n α).1 x  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
theorem fromTensorProduct_add
    (γ₁ γ₂ : ∀ x : B, Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                        Bundle.continuousMultilinearMap 𝕜 q F E x) (x : B) :
    fromTensor s q x (γ₁ x + γ₂ x) = fromTensor s q x (γ₁ x) + fromTensor s q x (γ₂ x)  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
theorem fromTensorProduct_smul
    (c : 𝕜) (γ : ∀ x : B, Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                    Bundle.continuousMultilinearMap 𝕜 q F E x) (x : B) :
    fromTensor s q x (c • γ x) = c • fromTensor s q x (γ x)  := by sorry

end BundleEquiv

end TensorProductInstances

end DifferentialGeometry.MultilinearSection

end

