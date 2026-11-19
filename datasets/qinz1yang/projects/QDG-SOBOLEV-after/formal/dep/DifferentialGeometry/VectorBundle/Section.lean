
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import dep.DifferentialGeometry.VectorBundle.Equiv
import dep.DifferentialGeometry.VectorBundle.Frame



set_option autoImplicit false

open scoped Manifold ContDiff
open Bundle



section ModuleOverSmoothFunctions

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞}
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

namespace ContMDiffSection


instance instSMulContMDiffMap : SMul C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ :=
  ⟨fun f s => ⟨fun x => f x • s x, f.2.smul_section s.contMDiff⟩⟩

@[simp]
theorem coe_smulContMDiffMap (f : C^n⟮I, M; 𝕜⟯) (s : Cₛ^n⟮I; F, V⟯) :
    ⇑(f • s) = fun x => f x • s x  := by sorry

instance instModuleContMDiffMap : Module C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ where
  one_smul s := by ext x; exact one_smul 𝕜 (s x)
  mul_smul f g s := by ext x; exact mul_smul (f x) (g x) (s x)
  smul_zero f := by ext x; exact smul_zero (f x)
  smul_add f s t := by ext x; exact smul_add (f x) (s x) (t x)
  add_smul f g s := by ext x; exact add_smul (f x) (g x) (s x)
  zero_smul s := by ext x; exact zero_smul 𝕜 (s x)

end ContMDiffSection

end ModuleOverSmoothFunctions



section MapSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞}
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : M → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : M → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

namespace ContMDiffVectorBundleHom


noncomputable def mapSection
    (Φ : ContMDiffVectorBundleHom 𝕜 I n F₁ E₁ F₂ E₂)
    (hΦ : Φ.baseMap = _root_.id) : Cₛ^n⟮I; F₁, E₁⟯ →ₗ[C^n⟮I, M; 𝕜⟯] Cₛ^n⟮I; F₂, E₂⟯ := by
  obtain ⟨baseMap, toFun, hc, φ, compat⟩ := Φ
  subst hΦ
  exact
  { toFun := fun σ =>
      ⟨fun x => φ x (σ x), (hc.comp σ.contMDiff).congr fun x => (compat x (σ x)).symm⟩
    map_add' := fun σ τ => by ext x; exact (φ x).map_add (σ x) (τ x)
    map_smul' := fun f σ => by ext x; exact (φ x).map_smul (f x) (σ x) }


theorem mapSection_apply :
    ∀ (Φ : ContMDiffVectorBundleHom 𝕜 I n F₁ E₁ F₂ E₂)
    (hΦ : Φ.baseMap = _root_.id) (σ : Cₛ^n⟮I; F₁, E₁⟯) (x : M),
    Φ.toFun ⟨x, σ x⟩ = ⟨x, (Φ.mapSection hΦ σ) x⟩
  | ⟨_, _, _, _, compat⟩, rfl, σ, x => compat x (σ x)


theorem tensorialAt
    (Φ : ContMDiffVectorBundleHom 𝕜 I n F₁ E₁ F₂ E₂) (x : M) :
    TensorialAt I F₁ (fun σ => Φ.fiberLinearMap x (σ x)) x  := by sorry

end ContMDiffVectorBundleHom



section SectionAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]


theorem ContMDiffSection.finset_sum_apply {ι : Type*} (s : Finset ι)
    (f : ι → Cₛ^n⟮I; F, V⟯) (x : M) :
    (∑ i ∈ s, f i : Cₛ^n⟮I; F, V⟯) x = ∑ i ∈ s, f i x  := by sorry

theorem ContMDiffSection.exists_eq_at
    [IsManifold I ∞ M] [T2Space M]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [ContMDiffVectorBundle n F V I]
    (p : M) (v : V p) : ∃ (σ : Cₛ^n⟮I; F, V⟯), σ p = v  := by sorry

end SectionAux





section ActsHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞} [h1n : Fact (1 ≤ n)]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  {E₁ : M → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℝ (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {E₂ : M → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module ℝ (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂]
  [IsManifold I ∞ M] [T2Space M]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F₁]
  [ContMDiffVectorBundle n F₁ E₁ I]

omit [FiniteDimensional ℝ F₁] [ContMDiffVectorBundle n F₁ E₁ I] h1n in

theorem ContMDiffVectorBundleHom.linearMap_acts_locally
    (F : Cₛ^n⟮I; F₁, E₁⟯ →ₗ[C^n⟮I, M; ℝ⟯] Cₛ^n⟮I; F₂, E₂⟯)
    (σ : Cₛ^n⟮I; F₁, E₁⟯) {U : Set M} (hU : IsOpen U)
    (hσU : ∀ x ∈ U, σ x = 0) : ∀ p ∈ U, (F σ) p = 0  := by sorry

theorem ContMDiffVectorBundleHom.linearMap_acts_pointwise
    (F : Cₛ^n⟮I; F₁, E₁⟯ →ₗ[C^n⟮I, M; ℝ⟯] Cₛ^n⟮I; F₂, E₂⟯)
    (σ₁ σ₂ : Cₛ^n⟮I; F₁, E₁⟯) (p : M) (hσ : σ₁ p = σ₂ p) :
    (F σ₁) p = (F σ₂) p  := by sorry

end ActsHelpers

section VBC

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞} [h1n : Fact (1 ≤ n)]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  {E₁ : M → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℝ (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {E₂ : M → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module ℝ (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂]
  [ContMDiffVectorBundle n F₁ E₁ I] [ContMDiffVectorBundle n F₂ E₂ I]


noncomputable def ContMDiffVectorBundleHom.ofLinearMapSection
    (F : Cₛ^n⟮I; F₁, E₁⟯ →ₗ[C^n⟮I, M; ℝ⟯] Cₛ^n⟮I; F₂, E₂⟯) :
    ContMDiffVectorBundleHom ℝ I n F₁ E₁ F₂ E₂ := by
  
  haveI : ContMDiffVectorBundle 1 F₁ E₁ I :=
    ContMDiffVectorBundle.of_le (show (1 : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) from
      WithTop.coe_le_coe.mpr h1n.out)
  haveI : ContMDiffVectorBundle 1 F₂ E₂ I :=
    ContMDiffVectorBundle.of_le (show (1 : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) from
      WithTop.coe_le_coe.mpr h1n.out)
  
  have acts_pointwise := ContMDiffVectorBundleHom.linearMap_acts_pointwise F
  
  have exists_section : ∀ (p : M) (v : E₁ p),
      ∃ (σ : Cₛ^n⟮I; F₁, E₁⟯), σ p = v := ContMDiffSection.exists_eq_at
  
  
  
  let φ : ∀ x : M, E₁ x →ₗ[ℝ] E₂ x := fun x =>
    { toFun := fun v => (F (exists_section x v).choose) x
      map_add' := fun v w => by
        
        
        let σ_v := (exists_section x v).choose
        let σ_w := (exists_section x w).choose
        let σ_vw := (exists_section x (v + w)).choose
        have hv : σ_v x = v := (exists_section x v).choose_spec
        have hw : σ_w x = w := (exists_section x w).choose_spec
        have h_add : (σ_v + σ_w) x = v + w := by
          simp [ContMDiffSection.coe_add, Pi.add_apply, hv, hw]
        calc (F σ_vw) x
            = (F (σ_v + σ_w)) x := acts_pointwise σ_vw (σ_v + σ_w) x
                ((exists_section x (v + w)).choose_spec ▸ h_add ▸ rfl)
          _ = (F σ_v) x + (F σ_w) x := by
                rw [map_add, ContMDiffSection.coe_add, Pi.add_apply]
      map_smul' := fun c v => by
        
        let σ_v := (exists_section x v).choose
        let σ_cv := (exists_section x (c • v)).choose
        have hv : σ_v x = v := (exists_section x v).choose_spec
        have h_smul : (c • σ_v) x = c • v := by
          simp [ContMDiffSection.coe_smul, Pi.smul_apply, hv]
        
        let c' : C^n⟮I, M; ℝ⟯ := ⟨fun _ => c, contMDiff_const⟩
        have hc_eq : c • σ_v = c' • σ_v := by sorry
        calc (F σ_cv) x
            = (F (c • σ_v)) x := acts_pointwise σ_cv (c • σ_v) x
                ((exists_section x (c • v)).choose_spec ▸ h_smul ▸ rfl)
          _ = c • (F σ_v) x := by
                rw [hc_eq, F.map_smul, ContMDiffSection.coe_smulContMDiffMap]; rfl }
  
  have φ_spec : ∀ (σ : Cₛ^n⟮I; F₁, E₁⟯) (x : M), φ x (σ x) = (F σ) x :=
    fun σ x => acts_pointwise _ σ x (exists_section x (σ x)).choose_spec
  
  
  
  have Φ_smooth : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) n
      (fun p : TotalSpace F₁ E₁ => (⟨p.proj, φ p.proj p.2⟩ : TotalSpace F₂ E₂)) := by sorry
  exact ⟨_root_.id, fun p => ⟨p.proj, φ p.proj p.2⟩, Φ_smooth, φ, fun _ _ => rfl⟩


theorem ContMDiffVectorBundleHom.ofLinearMapSection_baseMap
    (F : Cₛ^n⟮I; F₁, E₁⟯ →ₗ[C^n⟮I, M; ℝ⟯] Cₛ^n⟮I; F₂, E₂⟯) :
    (ofLinearMapSection F).baseMap = _root_.id  := by sorry

theorem ContMDiffVectorBundleHom.ofLinearMapSection_spec
    (F : Cₛ^n⟮I; F₁, E₁⟯ →ₗ[C^n⟮I, M; ℝ⟯] Cₛ^n⟮I; F₂, E₂⟯) (σ) :
    F σ = (ofLinearMapSection F).mapSection (ofLinearMapSection_baseMap F) σ  := by sorry

omit h1n in

theorem ContMDiffVectorBundleHom.ofLinearMapSection_mapSection
    (Φ Ψ : ContMDiffVectorBundleHom ℝ I n F₁ E₁ F₂ E₂)
    (hΦ : Φ.baseMap = _root_.id) (hΨ : Ψ.baseMap = _root_.id)
    (h_eq : ∀ σ, Φ.mapSection hΦ σ = Ψ.mapSection hΨ σ) :
    Φ.toFun = Ψ.toFun  := by sorry

noncomputable def ContMDiffVectorBundleEquiv.ofLinearEquivSection
    (F : Cₛ^n⟮I; F₁, E₁⟯ ≃ₗ[C^n⟮I, M; ℝ⟯] Cₛ^n⟮I; F₂, E₂⟯) :
    ContMDiffVectorBundleEquiv ℝ I n F₁ E₁ F₂ E₂ := by
  
  let Φ := ContMDiffVectorBundleHom.ofLinearMapSection F.toLinearMap
  let hΦ : Φ.baseMap = _root_.id :=
    ContMDiffVectorBundleHom.ofLinearMapSection_baseMap F.toLinearMap
  have hΦ_spec : ∀ σ, F σ = Φ.mapSection hΦ σ :=
    ContMDiffVectorBundleHom.ofLinearMapSection_spec F.toLinearMap
  let Ψ := ContMDiffVectorBundleHom.ofLinearMapSection F.symm.toLinearMap
  let hΨ : Ψ.baseMap = _root_.id :=
    ContMDiffVectorBundleHom.ofLinearMapSection_baseMap F.symm.toLinearMap
  have hΨ_spec : ∀ σ, F.symm σ = Ψ.mapSection hΨ σ :=
    ContMDiffVectorBundleHom.ofLinearMapSection_spec F.symm.toLinearMap
  
  have hΨΦ : ∀ p, Ψ.toFun (Φ.toFun p) = p := by
    intro ⟨x, v⟩
    obtain ⟨σ, rfl⟩ := ContMDiffSection.exists_eq_at (I := I) (F := F₁) (n := n) x v
    rw [Φ.mapSection_apply hΦ, Ψ.mapSection_apply hΨ (Φ.mapSection hΦ σ) x]
    congr 1
    exact DFunLike.congr_fun
      (show Ψ.mapSection hΨ (Φ.mapSection hΦ σ) = σ from by
        rw [← hΨ_spec, ← hΦ_spec]; simp) x
  have hΦΨ : ∀ p, Φ.toFun (Ψ.toFun p) = p := by
    intro ⟨x, v⟩
    obtain ⟨σ, rfl⟩ := ContMDiffSection.exists_eq_at (I := I) (F := F₂) (n := n) x v
    rw [Ψ.mapSection_apply hΨ, Φ.mapSection_apply hΦ (Ψ.mapSection hΨ σ) x]
    congr 1
    exact DFunLike.congr_fun
      (show Φ.mapSection hΦ (Ψ.mapSection hΨ σ) = σ from by
        rw [← hΦ_spec, ← hΨ_spec]; simp) x
  exact ContMDiffVectorBundleEquiv.ofMutualInverseHoms Φ Ψ hΦ hΨΦ hΦΨ

open FiberBundle in

noncomputable def ContMDiffVectorBundleHom.ofTensorialAt
    (Ψ : (Π x : M, E₁ x) → (Π x : M, E₂ x))
    (hΨ : ∀ x, TensorialAt I F₁ (fun σ => Ψ σ x) x)
    (hΨ_smooth : ∀ σ : Cₛ^n⟮I; F₁, E₁⟯,
      ContMDiff I (I.prod 𝓘(ℝ, F₂)) n (T% (Ψ ⇑σ))) :
    ContMDiffVectorBundleHom ℝ I n F₁ E₁ F₂ E₂ := by
  
  have h1n' : (1 : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) := WithTop.coe_le_coe.mpr h1n.out
  have hn_ne : (↑n : WithTop ℕ∞) ≠ 0 := (zero_lt_one.trans_le h1n').ne'
  haveI : ContMDiffVectorBundle 1 F₁ E₁ I := ContMDiffVectorBundle.of_le h1n'
  haveI : ContMDiffVectorBundle 1 F₂ E₂ I := ContMDiffVectorBundle.of_le h1n'
  
  
  let φ : ∀ x : M, E₁ x →ₗ[ℝ] E₂ x := fun x =>
    { toFun := fun v => Ψ (extend F₁ v) x
      map_add' := fun v₁ v₂ => by
        rw [← (hΨ x).add (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)]
        exact (hΨ x).pointwise (mdifferentiableAt_extend ..)
          (mdifferentiableAt_add_section (mdifferentiableAt_extend ..)
            (mdifferentiableAt_extend ..)) (by simp)
      map_smul' := fun c v => by
        dsimp
        rw [← (hΨ x).smul (f := fun _ => c) (mdifferentiable_const ..)
          (mdifferentiableAt_extend ..)]
        exact (hΨ x).pointwise (mdifferentiableAt_extend ..)
          (mdifferentiableAt_const.smul_section (mdifferentiableAt_extend ..)) (by simp) }
  
  have φ_spec : ∀ (σ : Cₛ^n⟮I; F₁, E₁⟯) (x : M), φ x (σ x) = Ψ (⇑σ) x :=
    fun σ x => (hΨ x).pointwise (mdifferentiableAt_extend ..)
      (σ.contMDiff.contMDiffAt.mdifferentiableAt hn_ne) (by simp)
  
  have Φ_smooth : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) n
      (fun p : TotalSpace F₁ E₁ => (⟨p.proj, φ p.proj p.2⟩ : TotalSpace F₂ E₂)) := by sorry
  exact ⟨_root_.id, fun p => ⟨p.proj, φ p.proj p.2⟩, Φ_smooth, φ, fun _ _ => rfl⟩

end VBC

end MapSection
