
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension
import dep.DifferentialGeometry.VectorBundle.Zero
import Mathlib.Geometry.Manifold.VectorBundle.Basic

set_option autoImplicit false



open Bundle




structure VectorBundleHom
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {B₁ : Type*} [TopologicalSpace B₁] {B₂ : Type*} [TopologicalSpace B₂]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    (E₁ : B₁ → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (E₂ : B₂ → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] where
  
  baseMap : B₁ → B₂
  
  toFun : TotalSpace F₁ E₁ → TotalSpace F₂ E₂
  
  continuous_toFun : Continuous toFun
  
  fiberLinearMap : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)
  
  fiber_compat : ∀ (x : B₁) (v : E₁ x),
    toFun ⟨x, v⟩ = ⟨baseMap x, fiberLinearMap x v⟩

namespace VectorBundleHom

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B₁ : Type*} [TopologicalSpace B₁]
  {B₂ : Type*} [TopologicalSpace B₂]
  {B₃ : Type*} [TopologicalSpace B₃]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)]
  {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {E₃ : B₃ → Type*} [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜 (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)]


def mk'
    (Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂) (hΦ : Continuous Φ)
    (φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ ((Φ ⟨x, 0⟩).proj))
    (hcompat : ∀ (x : B₁) (v : E₁ x),
      Φ ⟨x, v⟩ = ⟨(Φ ⟨x, 0⟩).proj, φ x v⟩) :
    VectorBundleHom 𝕜 F₁ E₁ F₂ E₂ where
  baseMap x := (Φ ⟨x, 0⟩).proj
  toFun := Φ
  continuous_toFun := hΦ
  fiberLinearMap := φ
  fiber_compat := hcompat

@[ext]
theorem ext (A B : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂)
    (h : A.toFun = B.toFun) : A = B  := by sorry

theorem baseMap_eq (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) (x : B₁) :
    f.baseMap x = (f.toFun ⟨x, 0⟩).proj  := by sorry

theorem baseMapContinuous
    [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]
    (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) : Continuous f.baseMap  := by sorry

@[simp]
theorem proj_eq (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) (p : TotalSpace F₁ E₁) :
    (f.toFun p).proj = f.baseMap p.proj  := by sorry

@[simp]
theorem toFun_apply (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) (x : B₁) (v : E₁ x) :
    f.toFun ⟨x, v⟩ = ⟨f.baseMap x, f.fiberLinearMap x v⟩  := by sorry

def id : VectorBundleHom 𝕜 F₁ E₁ F₁ E₁ where
  baseMap := _root_.id
  toFun := _root_.id
  continuous_toFun := continuous_id
  fiberLinearMap _ := LinearMap.id
  fiber_compat _ _ := rfl

def comp (g : VectorBundleHom 𝕜 F₂ E₂ F₃ E₃) (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) :
    VectorBundleHom 𝕜 F₁ E₁ F₃ E₃ where
  baseMap := g.baseMap ∘ f.baseMap
  toFun := g.toFun ∘ f.toFun
  continuous_toFun := g.continuous_toFun.comp f.continuous_toFun
  fiberLinearMap x := (g.fiberLinearMap (f.baseMap x)).comp (f.fiberLinearMap x)
  fiber_compat x v := by
    simp only [Function.comp_apply, f.fiber_compat, g.fiber_compat]
    congr 1

end VectorBundleHom




structure VectorBundleEquiv
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {B₁ : Type*} [TopologicalSpace B₁] {B₂ : Type*} [TopologicalSpace B₂]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    (E₁ : B₁ → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (E₂ : B₂ → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] where
  
  baseMap : B₁ → B₂
  
  toHomeomorph : TotalSpace F₁ E₁ ≃ₜ TotalSpace F₂ E₂
  
  fiberLinearEquiv : ∀ x : B₁, E₁ x ≃ₗ[𝕜] E₂ (baseMap x)
  
  fiber_compat : ∀ (x : B₁) (v : E₁ x),
    toHomeomorph ⟨x, v⟩ = ⟨baseMap x, fiberLinearEquiv x v⟩

namespace VectorBundleEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B₁ : Type*} [TopologicalSpace B₁]
  {B₂ : Type*} [TopologicalSpace B₂]
  {B₃ : Type*} [TopologicalSpace B₃]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)]
  {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {E₃ : B₃ → Type*} [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜 (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)]


def mk'
    (Φ : TotalSpace F₁ E₁ ≃ₜ TotalSpace F₂ E₂)
    (φ : ∀ x : B₁, E₁ x ≃ₗ[𝕜] E₂ ((Φ ⟨x, 0⟩).proj))
    (hcompat : ∀ (x : B₁) (v : E₁ x),
      Φ ⟨x, v⟩ = ⟨(Φ ⟨x, 0⟩).proj, φ x v⟩) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂ where
  baseMap x := (Φ ⟨x, 0⟩).proj
  toHomeomorph := Φ
  fiberLinearEquiv := φ
  fiber_compat := hcompat

@[ext]
theorem ext (A B : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂)
    (h : A.toHomeomorph = B.toHomeomorph) : A = B  := by sorry

theorem baseMap_eq (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (x : B₁) :
    e.baseMap x = (e.toHomeomorph ⟨x, 0⟩).proj  := by sorry

theorem baseMapBijective (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) :
    Function.Bijective e.baseMap  := by sorry

@[simp]
theorem proj_eq (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (p : TotalSpace F₁ E₁) :
    (e.toHomeomorph p).proj = e.baseMap p.proj  := by sorry

@[simp]
theorem toHomeomorph_apply (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (x : B₁) (v : E₁ x) :
    e.toHomeomorph ⟨x, v⟩ = ⟨e.baseMap x, e.fiberLinearEquiv x v⟩  := by sorry

def toVectorBundleHom (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) :
    VectorBundleHom 𝕜 F₁ E₁ F₂ E₂ where
  baseMap := e.baseMap
  toFun := e.toHomeomorph
  continuous_toFun := e.toHomeomorph.continuous
  fiberLinearMap x := (e.fiberLinearEquiv x).toLinearMap
  fiber_compat x v := e.fiber_compat x v

def refl : VectorBundleEquiv 𝕜 F₁ E₁ F₁ E₁ where
  baseMap := _root_.id
  toHomeomorph := Homeomorph.refl _
  fiberLinearEquiv x := LinearEquiv.refl 𝕜 (E₁ x)
  fiber_compat _ _ := rfl

def symm (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) :
    VectorBundleEquiv 𝕜 F₂ E₂ F₁ E₁ where
  baseMap y := (e.toHomeomorph.symm ⟨y, 0⟩).proj
  toHomeomorph := e.toHomeomorph.symm
  fiberLinearEquiv y :=
    
    let x := (e.toHomeomorph.symm ⟨y, 0⟩).proj
    have hx : e.baseMap x = y := by
      have := e.proj_eq (e.toHomeomorph.symm ⟨y, 0⟩)
      rw [e.toHomeomorph.apply_symm_apply] at this; exact this.symm
    (hx ▸ e.fiberLinearEquiv x).symm
  fiber_compat y v := by
    have key : ∀ (x : B₁) (hx : e.baseMap x = y),
        (⟨y, v⟩ : TotalSpace F₂ E₂) =
        ⟨e.baseMap x, e.fiberLinearEquiv x ((hx ▸ e.fiberLinearEquiv x).symm v)⟩ := by
      intro x hx; subst hx; simp [LinearEquiv.apply_symm_apply]
    apply e.toHomeomorph.injective
    rw [e.toHomeomorph.apply_symm_apply, e.toHomeomorph_apply]
    exact key _ _

def trans (e₁₂ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (e₂₃ : VectorBundleEquiv 𝕜 F₂ E₂ F₃ E₃) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₃ E₃ where
  baseMap := e₂₃.baseMap ∘ e₁₂.baseMap
  toHomeomorph := e₁₂.toHomeomorph.trans e₂₃.toHomeomorph
  fiberLinearEquiv x := (e₁₂.fiberLinearEquiv x).trans (e₂₃.fiberLinearEquiv (e₁₂.baseMap x))
  fiber_compat x v := by
    simp only [Homeomorph.trans_apply, e₁₂.fiber_compat, e₂₃.fiber_compat, Function.comp]
    congr 1

end VectorBundleEquiv



section TrivializationCoord

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {B₁ : Type*} [TopologicalSpace B₁]
  {B₂ : Type*} [TopologicalSpace B₂]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]


noncomputable def trivializationCoord (baseMap : B₁ → B₂)
    (φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)) (x : B₁) : B₁ → (F₁ →L[𝕜] F₂) := by
  classical
  exact fun q =>
    if hq : q ∈ (trivializationAt F₁ E₁ x).baseSet ∧
        baseMap q ∈ (trivializationAt F₂ E₂ (baseMap x)).baseSet then
      LinearMap.toContinuousLinearMap
        (((trivializationAt F₂ E₂ (baseMap x)).continuousLinearEquivAt
          𝕜 (baseMap q) hq.2).toLinearMap.comp
          ((φ q).comp
            ((trivializationAt F₁ E₁ x).continuousLinearEquivAt 𝕜 q hq.1).symm.toLinearMap))
    else 0


lemma trivializationCoord_apply
    {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂}
    {baseMap : B₁ → B₂}
    {φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)}
    (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨baseMap x, φ x v⟩)
    (x q : B₁)
    (hq₁ : q ∈ (trivializationAt F₁ E₁ x).baseSet)
    (hq₂ : baseMap q ∈ (trivializationAt F₂ E₂ (baseMap x)).baseSet)
    (v : F₁) :
    trivializationCoord baseMap φ x q v =
      ((trivializationAt F₂ E₂ (baseMap x))
        (Φ ((trivializationAt F₁ E₁ x).toOpenPartialHomeomorph.symm (q, v)))).2  := by sorry

lemma trivializationCoord_isInvertible
    {baseMap : B₁ → B₂}
    {φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)}
    (hφ_bij : ∀ x, Function.Bijective (φ x))
    (x q : B₁)
    (hq : q ∈ (trivializationAt F₁ E₁ x).baseSet ∧
      baseMap q ∈ (trivializationAt F₂ E₂ (baseMap x)).baseSet) :
    (trivializationCoord baseMap φ x q : F₁ →L[𝕜] F₂).IsInvertible  := by sorry

lemma trivializationCoord_inverse_eventuallyEq
    {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂}
    (baseMap : B₁ ≃ₜ B₂)
    {φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)}
    (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨baseMap x, φ x v⟩)
    (hbij : Function.Bijective Φ) (hφ_bij : ∀ x, Function.Bijective (φ x))
    (x : B₁) (w : E₂ (baseMap x)) :
    (fun p : B₂ × F₂ =>
        ContinuousLinearMap.inverse
          (trivializationCoord baseMap φ x (baseMap.symm p.1)) p.2)
      =ᶠ[nhds ((trivializationAt F₂ E₂ (baseMap x)) ⟨baseMap x, w⟩)]
    (fun p : B₂ × F₂ => ((trivializationAt F₁ E₁ x)
      ((Equiv.ofBijective Φ hbij).symm
        ((trivializationAt F₂ E₂ (baseMap x)).toOpenPartialHomeomorph.symm p))).2)  := by sorry

end TrivializationCoord





section ToVectorBundleEquivGeneral

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {B₁ : Type*} [TopologicalSpace B₁]
  {B₂ : Type*} [TopologicalSpace B₂]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [TopologicalSpace B₁] [TopologicalSpace B₂]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] in

private lemma fiberBijective_of_bijective'
    {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂}
    {baseMap : B₁ → B₂}
    {φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)}
    (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨baseMap x, φ x v⟩)
    (hbij : Function.Bijective Φ)
    (hbase_inj : Function.Injective baseMap)
    (x : B₁) :
    Function.Bijective (φ x)  := by sorry

private lemma continuousAt_clm_of_pointwise
    {X : Type*} [TopologicalSpace X]
    {A : X → (F₁ →L[𝕜] F₂)} {x : X}
    (h : ∀ v, ContinuousAt (fun q => A q v) x) :
    ContinuousAt A x  := by sorry

private lemma continuous_symm_of_fiberBijective'
    {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂} (hΦ_cont : Continuous Φ)
    (baseMap : B₁ ≃ₜ B₂)
    {φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)}
    (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨baseMap x, φ x v⟩)
    (hbij : Function.Bijective Φ) (hφ_bij : ∀ x, Function.Bijective (φ x)) :
    Continuous (Equiv.ofBijective Φ hbij).symm  := by sorry

noncomputable def VectorBundleHom.toVectorBundleEquiv
    (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂)
    (baseMap : B₁ ≃ₜ B₂)
    (hbase : f.baseMap = baseMap)
    (hbij : Function.Bijective f.toFun) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂ := by
  obtain ⟨bm, Φ, hΦ_cont, φ, hcompat⟩ := f
  simp only at hbase
  subst hbase
  change Function.Bijective Φ at hbij
  have hcompat' : ∀ x v, Φ ⟨x, v⟩ = (⟨baseMap x, φ x v⟩ : TotalSpace F₂ E₂) := hcompat
  have hφ_bij : ∀ x, Function.Bijective (φ x) :=
    fiberBijective_of_bijective' hcompat' hbij baseMap.injective
  exact {
    baseMap := baseMap
    toHomeomorph := ⟨Equiv.ofBijective Φ hbij, hΦ_cont,
      continuous_symm_of_fiberBijective' hΦ_cont baseMap hcompat' hbij hφ_bij⟩
    fiberLinearEquiv := fun x => LinearEquiv.ofBijective (φ x) (hφ_bij x)
    fiber_compat := fun x v => hcompat' x v
  }

end ToVectorBundleEquivGeneral



section ToVectorBundleEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {B : Type*} [TopologicalSpace B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]


private lemma continuous_symm_of_fiberBijective
    {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂} (hΦ_cont : Continuous Φ)
    {φ : ∀ x, E₁ x →ₗ[𝕜] E₂ x}
    (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨x, φ x v⟩)
    (hbij : Function.Bijective Φ) (hφ_bij : ∀ x, Function.Bijective (φ x)) :
    Continuous (Equiv.ofBijective Φ hbij).symm  := by sorry

noncomputable def VectorBundleHom.toVectorBundleEquivId
    (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂)
    (hid : f.baseMap = _root_.id)
    (hbij : Function.Bijective f.toFun) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂ :=
  f.toVectorBundleEquiv (Homeomorph.refl B) hid hbij

end ToVectorBundleEquiv



open scoped Manifold


structure ContMDiffVectorBundleEquiv
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
    {HB : Type*} [TopologicalSpace HB]
    (IB : ModelWithCorners 𝕜 EB HB)
    (n : WithTop ℕ∞)
    {B₁ : Type*} [TopologicalSpace B₁] [ChartedSpace HB B₁]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    (E₁ : B₁ → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
    [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    {B₂ : Type*} [TopologicalSpace B₂] [ChartedSpace HB B₂]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (E₂ : B₂ → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂] where
  baseMap : B₁ → B₂
  toDiffeomorph : Diffeomorph (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂))
    (TotalSpace F₁ E₁) (TotalSpace F₂ E₂) n
  fiberLinearEquiv : ∀ x : B₁, E₁ x ≃ₗ[𝕜] E₂ (baseMap x)
  fiber_compat : ∀ (x : B₁) (v : E₁ x),
    toDiffeomorph ⟨x, v⟩ = ⟨baseMap x, fiberLinearEquiv x v⟩

namespace ContMDiffVectorBundleEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {n : WithTop ℕ∞}
  {B₁ : Type*} [TopologicalSpace B₁] [ChartedSpace HB B₁]
  {B₂ : Type*} [TopologicalSpace B₂] [ChartedSpace HB B₂]
  {B₃ : Type*} [TopologicalSpace B₃] [ChartedSpace HB B₃]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {E₃ : B₃ → Type*} [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜 (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)] [∀ x, TopologicalSpace (E₃ x)]
  [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]


def mk'
    (Φ : Diffeomorph (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂))
      (TotalSpace F₁ E₁) (TotalSpace F₂ E₂) n)
    (φ : ∀ x : B₁, E₁ x ≃ₗ[𝕜] E₂ ((Φ ⟨x, 0⟩).proj))
    (hcompat : ∀ (x : B₁) (v : E₁ x),
      Φ ⟨x, v⟩ = ⟨(Φ ⟨x, 0⟩).proj, φ x v⟩) :
    ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂ where
  baseMap x := (Φ ⟨x, 0⟩).proj
  toDiffeomorph := Φ
  fiberLinearEquiv := φ
  fiber_compat := hcompat

@[ext]
theorem ext (A B : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂)
    (h : A.toDiffeomorph = B.toDiffeomorph) : A = B  := by sorry

theorem baseMap_eq (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) (x : B₁) :
    e.baseMap x = (e.toDiffeomorph ⟨x, 0⟩).proj  := by sorry

theorem baseMapBijective (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) :
    Function.Bijective e.baseMap  := by sorry

def toVectorBundleEquiv (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂ where
  baseMap := e.baseMap
  toHomeomorph := e.toDiffeomorph.toHomeomorph
  fiberLinearEquiv := e.fiberLinearEquiv
  fiber_compat x v := e.fiber_compat x v

@[simp]
theorem proj_eq (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂)
    (p : TotalSpace F₁ E₁) : (e.toDiffeomorph p).proj = e.baseMap p.proj  := by sorry

@[simp]
theorem toDiffeomorph_apply (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂)
    (x : B₁) (v : E₁ x) :
    e.toDiffeomorph ⟨x, v⟩ = ⟨e.baseMap x, e.fiberLinearEquiv x v⟩  := by sorry

def refl : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₁ E₁ where
  baseMap := _root_.id
  toDiffeomorph := Diffeomorph.refl (IB.prod 𝓘(𝕜, F₁)) (TotalSpace F₁ E₁) n
  fiberLinearEquiv x := LinearEquiv.refl 𝕜 (E₁ x)
  fiber_compat _ _ := rfl

def symm (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) :
    ContMDiffVectorBundleEquiv 𝕜 IB n F₂ E₂ F₁ E₁ where
  baseMap y := (e.toDiffeomorph.symm ⟨y, 0⟩).proj
  toDiffeomorph := e.toDiffeomorph.symm
  fiberLinearEquiv y :=
    let x := (e.toDiffeomorph.symm ⟨y, 0⟩).proj
    have hx : e.baseMap x = y := by
      have := e.proj_eq (e.toDiffeomorph.symm ⟨y, 0⟩)
      simp [e.toDiffeomorph.apply_symm_apply] at this; exact this.symm
    (hx ▸ e.fiberLinearEquiv x).symm
  fiber_compat y v := by exact e.toVectorBundleEquiv.symm.fiber_compat y v

def trans (e₁₂ : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂)
    (e₂₃ : ContMDiffVectorBundleEquiv 𝕜 IB n F₂ E₂ F₃ E₃) :
    ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₃ E₃ where
  baseMap := e₂₃.baseMap ∘ e₁₂.baseMap
  toDiffeomorph := e₁₂.toDiffeomorph.trans e₂₃.toDiffeomorph
  fiberLinearEquiv x :=
    (e₁₂.fiberLinearEquiv x).trans (e₂₃.fiberLinearEquiv (e₁₂.baseMap x))
  fiber_compat x v := by
    simp only [Diffeomorph.coe_trans, Function.comp_apply, e₁₂.fiber_compat, e₂₃.fiber_compat]
    congr 1

end ContMDiffVectorBundleEquiv




structure ContMDiffVectorBundleHom
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
    {HB : Type*} [TopologicalSpace HB]
    (IB : ModelWithCorners 𝕜 EB HB)
    (n : WithTop ℕ∞)
    {B₁ : Type*} [TopologicalSpace B₁] [ChartedSpace HB B₁]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    (E₁ : B₁ → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
    [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    {B₂ : Type*} [TopologicalSpace B₂] [ChartedSpace HB B₂]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (E₂ : B₂ → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂] where
  baseMap : B₁ → B₂
  toFun : TotalSpace F₁ E₁ → TotalSpace F₂ E₂
  contMDiff_toFun : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n toFun
  fiberLinearMap : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)
  fiber_compat : ∀ (x : B₁) (v : E₁ x),
    toFun ⟨x, v⟩ = ⟨baseMap x, fiberLinearMap x v⟩

namespace ContMDiffVectorBundleHom

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {n : WithTop ℕ∞}
  {B₁ : Type*} [TopologicalSpace B₁] [ChartedSpace HB B₁]
  {B₂ : Type*} [TopologicalSpace B₂] [ChartedSpace HB B₂]
  {B₃ : Type*} [TopologicalSpace B₃] [ChartedSpace HB B₃]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {E₃ : B₃ → Type*} [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜 (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)] [∀ x, TopologicalSpace (E₃ x)]
  [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]


def mk'
    (Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂)
    (hΦ : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n Φ)
    (φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ ((Φ ⟨x, 0⟩).proj))
    (hcompat : ∀ (x : B₁) (v : E₁ x),
      Φ ⟨x, v⟩ = ⟨(Φ ⟨x, 0⟩).proj, φ x v⟩) :
    ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂ where
  baseMap x := (Φ ⟨x, 0⟩).proj
  toFun := Φ
  contMDiff_toFun := hΦ
  fiberLinearMap := φ
  fiber_compat := hcompat

@[ext]
theorem ext (A B : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂)
    (h : A.toFun = B.toFun) : A = B  := by sorry

theorem baseMap_eq (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂) (x : B₁) :
    f.baseMap x = (f.toFun ⟨x, 0⟩).proj  := by sorry

theorem baseMapContMDiff [ContMDiffVectorBundle n F₁ E₁ IB]
    (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂) :
    ContMDiff IB IB n f.baseMap  := by sorry

def toVectorBundleHom (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂) :
    VectorBundleHom 𝕜 F₁ E₁ F₂ E₂ where
  baseMap := f.baseMap
  toFun := f.toFun
  continuous_toFun := f.contMDiff_toFun.continuous
  fiberLinearMap := f.fiberLinearMap
  fiber_compat x v := f.fiber_compat x v

@[simp]
theorem proj_eq (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂)
    (p : TotalSpace F₁ E₁) :
    (f.toFun p).proj = f.baseMap p.proj  := by sorry

@[simp]
theorem toFun_apply (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂)
    (x : B₁) (v : E₁ x) :
    f.toFun ⟨x, v⟩ = ⟨f.baseMap x, f.fiberLinearMap x v⟩  := by sorry

def id : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₁ E₁ where
  baseMap := _root_.id
  toFun := _root_.id
  contMDiff_toFun := contMDiff_id
  fiberLinearMap _ := LinearMap.id
  fiber_compat _ _ := rfl

def comp (g : ContMDiffVectorBundleHom 𝕜 IB n F₂ E₂ F₃ E₃)
    (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂) :
    ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₃ E₃ where
  baseMap := g.baseMap ∘ f.baseMap
  toFun := g.toFun ∘ f.toFun
  contMDiff_toFun := g.contMDiff_toFun.comp f.contMDiff_toFun
  fiberLinearMap x := (g.fiberLinearMap (f.baseMap x)).comp (f.fiberLinearMap x)
  fiber_compat x v := by
    simp only [Function.comp_apply, f.fiber_compat, g.fiber_compat]
    congr 1

def ofEquiv (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) :
    ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂ where
  baseMap := e.baseMap
  toFun := e.toDiffeomorph
  contMDiff_toFun := e.toDiffeomorph.contMDiff
  fiberLinearMap x := (e.fiberLinearEquiv x).toLinearMap
  fiber_compat x v := e.fiber_compat x v

end ContMDiffVectorBundleHom





section ToContMDiffVectorBundleEquivGeneral

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {n : WithTop ℕ∞}
  {B₁ : Type*} [TopologicalSpace B₁] [ChartedSpace HB B₁]
  {B₂ : Type*} [TopologicalSpace B₂] [ChartedSpace HB B₂]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [ContMDiffVectorBundle n F₁ E₁ IB]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [ContMDiffVectorBundle n F₂ E₂ IB]


lemma contMDiffAt_clm_of_pointwise
    {X : Type*} [TopologicalSpace X] [ChartedSpace HB X]
    {A : X → (F₁ →L[𝕜] F₂)} {x : X}
    (h : ∀ v, ContMDiffAt IB 𝓘(𝕜, F₂) n (fun q => A q v) x) :
    ContMDiffAt IB 𝓘(𝕜, F₁ →L[𝕜] F₂) n A x  := by sorry

private lemma contMDiff_symm_of_fiberBijective'
    {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂}
    (hΦ_smooth : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n Φ)
    (baseMap : Diffeomorph IB IB B₁ B₂ n)
    {φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)}
    (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨baseMap x, φ x v⟩)
    (hbij : Function.Bijective Φ) (hφ_bij : ∀ x, Function.Bijective (φ x)) :
    ContMDiff (IB.prod 𝓘(𝕜, F₂)) (IB.prod 𝓘(𝕜, F₁)) n
      (Equiv.ofBijective Φ hbij).symm  := by sorry

noncomputable def ContMDiffVectorBundleHom.toContMDiffVectorBundleEquiv
    (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂)
    (baseMap : Diffeomorph IB IB B₁ B₂ n)
    (hbase : f.baseMap = baseMap)
    (hbij : Function.Bijective f.toFun) :
    ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂ := by
  obtain ⟨bm, Φ, hΦ_smooth, φ, hcompat⟩ := f
  simp only at hbase
  subst hbase
  change Function.Bijective Φ at hbij
  have hcompat' : ∀ x v, Φ ⟨x, v⟩ = (⟨baseMap x, φ x v⟩ : TotalSpace F₂ E₂) := hcompat
  have hφ_bij : ∀ x, Function.Bijective (φ x) :=
    fiberBijective_of_bijective' hcompat' hbij baseMap.injective
  exact {
    baseMap := baseMap
    toDiffeomorph :=
      { toEquiv := Equiv.ofBijective Φ hbij
        contMDiff_toFun := hΦ_smooth
        contMDiff_invFun :=
          contMDiff_symm_of_fiberBijective' hΦ_smooth baseMap hcompat' hbij hφ_bij }
    fiberLinearEquiv := fun x => LinearEquiv.ofBijective (φ x) (hφ_bij x)
    fiber_compat := fun x v => hcompat' x v
  }

end ToContMDiffVectorBundleEquivGeneral



section ToContMDiffVectorBundleEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [ContMDiffVectorBundle n F₁ E₁ IB]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [ContMDiffVectorBundle n F₂ E₂ IB]


private lemma contMDiff_symm_of_fiberBijective
    {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂}
    (hΦ_smooth : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n Φ)
    {φ : ∀ x, E₁ x →ₗ[𝕜] E₂ x}
    (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨x, φ x v⟩)
    (hbij : Function.Bijective Φ) (hφ_bij : ∀ x, Function.Bijective (φ x)) :
    ContMDiff (IB.prod 𝓘(𝕜, F₂)) (IB.prod 𝓘(𝕜, F₁)) n
      (Equiv.ofBijective Φ hbij).symm  := by sorry

noncomputable def ContMDiffVectorBundleHom.toContMDiffVectorBundleEquivId
    (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂)
    (hid : f.baseMap = _root_.id)
    (hbij : Function.Bijective f.toFun) :
    ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂ :=
  f.toContMDiffVectorBundleEquiv (Diffeomorph.refl IB B n) hid hbij




section FiberwiseEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]


def ContMDiffVectorBundleHom.ofFiberwiseLinearMap
    {B₂ : Type*} [TopologicalSpace B₂] [ChartedSpace HB B₂]
    {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
    (f : B → B₂)
    (φ : ∀ x : B, E₁ x →ₗ[𝕜] E₂ (f x))
    (h_smooth : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n
      (fun p : TotalSpace F₁ E₁ => (⟨f p.1, φ p.1 p.2⟩ : TotalSpace F₂ E₂))) :
    ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂ where
  baseMap := f
  toFun p := ⟨f p.1, φ p.1 p.2⟩
  contMDiff_toFun := h_smooth
  fiberLinearMap := φ
  fiber_compat _ _ := rfl


noncomputable def ContMDiffVectorBundleEquiv.ofMutualInverseHoms
    (Φ : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂)
    (Ψ : ContMDiffVectorBundleHom 𝕜 IB n F₂ E₂ F₁ E₁)
    (hΦ : Φ.baseMap = _root_.id)
    (hΨΦ : ∀ p, Ψ.toFun (Φ.toFun p) = p)
    (hΦΨ : ∀ p, Φ.toFun (Ψ.toFun p) = p) :
    ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂ :=
  have hΨ : Ψ.baseMap = _root_.id := by
    funext y
    have h := congrArg TotalSpace.proj (hΦΨ ⟨y, 0⟩)
    rwa [Φ.proj_eq, Ψ.proj_eq, hΦ] at h
  match Φ, Ψ, hΦ, hΨ, hΨΦ, hΦΨ with
  | ⟨_, toFunΦ, hcΦ, φ, compatΦ⟩, ⟨_, toFunΨ, hcΨ, ψ, compatΨ⟩,
    rfl, rfl, hΨΦ, hΦΨ =>
    { baseMap := _root_.id
      toDiffeomorph :=
        { toEquiv := ⟨toFunΦ, toFunΨ, hΨΦ, hΦΨ⟩
          contMDiff_toFun := hcΦ
          contMDiff_invFun := hcΨ }
      fiberLinearEquiv := fun x =>
        LinearEquiv.ofLinear (φ x) (ψ x)
          (LinearMap.ext fun v => by
            have h := hΦΨ ⟨x, v⟩
            simp only [compatΦ, compatΨ] at h
            exact eq_of_heq (TotalSpace.mk.inj h).2)
          (LinearMap.ext fun v => by
            have h := hΨΦ ⟨x, v⟩
            simp only [compatΦ, compatΨ] at h
            exact eq_of_heq (TotalSpace.mk.inj h).2)
      fiber_compat := compatΦ }


noncomputable def ContMDiffVectorBundleEquiv.ofFiberwiseLinearEquiv
    (φ : ∀ x : B, E₁ x ≃ₗ[𝕜] E₂ x)
    (h_smooth : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n
      (fun p : TotalSpace F₁ E₁ => (⟨p.1, φ p.1 p.2⟩ : TotalSpace F₂ E₂)))
    (h_smooth_inv : ContMDiff (IB.prod 𝓘(𝕜, F₂)) (IB.prod 𝓘(𝕜, F₁)) n
      (fun p : TotalSpace F₂ E₂ => (⟨p.1, (φ p.1).symm p.2⟩ : TotalSpace F₁ E₁))) :
    ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂ where
  baseMap := _root_.id
  toDiffeomorph :=
    { toEquiv :=
        { toFun := fun p => ⟨p.1, φ p.1 p.2⟩
          invFun := fun p => ⟨p.1, (φ p.1).symm p.2⟩
          left_inv := fun ⟨_, v⟩ => by simp
          right_inv := fun ⟨_, v⟩ => by simp }
      contMDiff_toFun := h_smooth
      contMDiff_invFun := h_smooth_inv }
  fiberLinearEquiv := φ
  fiber_compat _ _ := rfl

end FiberwiseEquiv

end ToContMDiffVectorBundleEquiv
