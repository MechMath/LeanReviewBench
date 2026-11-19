import dep.DifferentialGeometry.Synthetic.Realization.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Hom



noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Bundle

section Embedding

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]


noncomputable def vectorFieldAction
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : C^∞⟮I, M; ℝ⟯) : M → ℝ :=
  fun x => extDerivFun (I := I) f x (X x)


noncomputable def vectorFieldActionSmooth
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : C^∞⟮I, M; ℝ⟯) : C^∞⟮I, M; ℝ⟯ :=
  ⟨vectorFieldAction I M X f, by
    intro x₀
    
    have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := f.2
    have htangent : ContMDiff (I.prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (tangentMap I 𝓘(ℝ, ℝ) f) := by
      apply ContMDiff.contMDiff_tangentMap hf
      simp
    
    have hcomp : ContMDiffAt I (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun x => tangentMap I 𝓘(ℝ, ℝ) f ⟨x, X x⟩) x₀ :=
      (htangent.contMDiffAt).comp x₀ (X.contMDiff.contMDiffAt)
    
    rw [contMDiffAt_totalSpace] at hcomp
    obtain ⟨_, hfiber⟩ := hcomp
    
    
    
    convert hfiber using 1
    ext x
    simp only [vectorFieldAction, extDerivFun, tangentMap,
      trivializationAt_model_space_apply]
    rfl⟩




theorem contMDiffMap_mdifferentiableAt (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) f x  := by sorry

theorem vectorFieldActionSmooth_add
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f g : C^∞⟮I, M; ℝ⟯) :
    vectorFieldActionSmooth I M X (f + g) =
      vectorFieldActionSmooth I M X f + vectorFieldActionSmooth I M X g  := by sorry

theorem vectorFieldActionSmooth_smul
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (c : ℝ) (f : C^∞⟮I, M; ℝ⟯) :
    vectorFieldActionSmooth I M X (c • f) =
      c • vectorFieldActionSmooth I M X f  := by sorry

theorem vectorFieldActionSmooth_leibniz
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f g : C^∞⟮I, M; ℝ⟯) :
    vectorFieldActionSmooth I M X (f * g) =
      f * vectorFieldActionSmooth I M X g + g * vectorFieldActionSmooth I M X f  := by sorry

theorem vectorFieldActionSmooth_map_one_eq_zero
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    vectorFieldActionSmooth I M X 1 = 0  := by sorry

noncomputable def embedDeriv
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ where
  toLinearMap :=
    { toFun := vectorFieldActionSmooth I M X
      map_add' := vectorFieldActionSmooth_add I M X
      map_smul' := fun c f => by
        simp only [RingHom.id_apply]
        exact vectorFieldActionSmooth_smul I M X c f }
  leibniz' f g := by
    change vectorFieldActionSmooth I M X (f * g) =
      f • vectorFieldActionSmooth I M X g + g • vectorFieldActionSmooth I M X f
    rw [vectorFieldActionSmooth_leibniz I M X f g]
    simp [smul_eq_mul]
  map_one_eq_zero' := by
    change vectorFieldActionSmooth I M X 1 = 0
    exact vectorFieldActionSmooth_map_one_eq_zero I M X




theorem embedDeriv_add
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    embedDeriv I M (X + Y) = embedDeriv I M X + embedDeriv I M Y  := by sorry

theorem embedDeriv_smul
    (φ : C^∞⟮I, M; ℝ⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    embedDeriv I M (φ • X) = φ • embedDeriv I M X  := by sorry

noncomputable def embedLinearMap :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯]
      Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ where
  toFun := embedDeriv I M
  map_add' := embedDeriv_add I M
  map_smul' := embedDeriv_smul I M




private theorem mfderiv_extChartAt_ne_zero
    {x₀ : M} (v : TangentSpace I x₀) (hv : v ≠ 0) :
    mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) x₀ v ≠ 0  := by sorry

theorem embedLinearMap_injective :
    Function.Injective (embedLinearMap I M)  := by sorry

noncomputable def mlieBracketSection
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨VectorField.mlieBracket I X Y, by
    have hX := X.contMDiff
    have hY := Y.contMDiff
    
    
    
    
    
    
    
    haveI : IsManifold I (minSmoothness ℝ 2) M := by
      rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
    haveI : IsManifold I (minSmoothness ℝ 3) M := by
      rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
    
    
    
    
    
    
    
    
    
    
    haveI : IsManifold I ((⊤ : ℕ∞) + 1) M := by
      have : ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) = ∞ := by
        show ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) = ∞
        simp
      exact this ▸ ‹IsManifold I ∞ M›
    exact ContDiff.mlieBracket_vectorField (I := I) (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞))
      hX hY (by
        rw [minSmoothness_of_isRCLikeNormedField]
        show ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) ≤ ∞
        simp)⟩


theorem embedDeriv_mlieBracket
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f : C^∞⟮I, M; ℝ⟯) :
    embedDeriv I M (mlieBracketSection I M X Y) f =
      embedDeriv I M X (embedDeriv I M Y f) -
      embedDeriv I M Y (embedDeriv I M X f)  := by sorry

theorem embed_bracket_closed
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∃ Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
      embedLinearMap I M Z = ⁅embedLinearMap I M X, embedLinearMap I M Y⁆  := by sorry

end Embedding

end
