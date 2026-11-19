
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.BumpFunction



set_option autoImplicit false

open scoped Manifold Topology ContDiff
open Bundle Filter

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
    [IsScalarTower ℝ 𝕜 F]
  {n : ℕ∞}
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, IsScalarTower ℝ 𝕜 (V x)]
  [VectorBundle ℝ F V]

variable {ι : Type*} {s : ι → (x : M) → V x} {u : Set M} {p : M}


theorem exists_contMDiffSection_eqOn_nhd
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [ContMDiffVectorBundle n F V I] [IsManifold I ∞ M] [T2Space M]
    (hs : ∀ i, CMDiff[u] n (T% (s i))) (hu : IsOpen u) (hp : p ∈ u) :
    ∃ (s' : ι → Cₛ^n⟮I; F, V⟯), ∀ᶠ x in 𝓝 p, ∀ i, s' i x = s i x  := by sorry

theorem IsLocalFrameOn.exists_contMDiffSection_eqOn_nhd
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [ContMDiffVectorBundle n F V I] [IsManifold I ∞ M] [T2Space M]
    (hs : IsLocalFrameOn I F n s u) (hu : IsOpen u) (hp : p ∈ u) :
    ∃ (s' : ι → Cₛ^n⟮I; F, V⟯), ∀ᶠ x in 𝓝 p, ∀ i, s' i x = s i x  := by sorry

