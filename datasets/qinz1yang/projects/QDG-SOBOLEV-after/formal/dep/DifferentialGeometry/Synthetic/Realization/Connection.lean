import dep.DifferentialGeometry.Synthetic.Realization.Embedding
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion



noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Bundle CovariantDerivative

section Connection

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]




noncomputable def concreteConn
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ where
  toFun x := cov Y x (X x)
  contMDiff_toFun := by
    
    
    have hY_plus : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ + 1) (T% fun x => Y x) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from by simp]
      exact Y.contMDiff
    have hcov_smooth := (‹ContMDiffCovariantDerivative cov ∞›).contMDiff.contMDiff
      (hY_plus.contMDiffOn)
    
    
    
    have hcov_global : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun x => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun (x : M) => TangentSpace I x →L[ℝ] TangentSpace I x) x (cov Y x)) := by
      rwa [← contMDiffOn_univ]
    
    have hX_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x => TotalSpace.mk' E (E := TangentSpace I) x (X x)) :=
      X.contMDiff
    
    exact ContMDiff.clm_bundle_apply (b := id) hcov_global hX_smooth


theorem concreteConn_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    concreteConn I M cov X Y x = cov Y x (X x)  := by sorry

theorem concreteConn_add_right
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    concreteConn I M cov X (Y + Z) = concreteConn I M cov X Y + concreteConn I M cov X Z  := by sorry

theorem concreteConn_add_left
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    concreteConn I M cov (X + Y) Z = concreteConn I M cov X Z + concreteConn I M cov Y Z  := by sorry

theorem concreteConn_smul_left
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (f : C^∞⟮I, M; ℝ⟯)
    (X Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    concreteConn I M cov (f • X) Z = f • concreteConn I M cov X Z  := by sorry

theorem concreteConn_leibniz
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f : C^∞⟮I, M; ℝ⟯)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    concreteConn I M cov X (f • Y) =
      vectorFieldActionSmooth I M X f • Y + f • concreteConn I M cov X Y  := by sorry

noncomputable def concreteDerivationEmbedding :
    DerivationEmbedding ℝ C^∞⟮I, M; ℝ⟯
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ where
  embed := embedLinearMap I M
  embed_injective := embedLinearMap_injective I M
  bracket_closed := embed_bracket_closed I M


theorem bracket_eq_mlieBracketSection
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    bracket (concreteDerivationEmbedding I M) X Y = mlieBracketSection I M X Y  := by sorry

theorem concreteConn_torsion_free
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (h_tf : cov.torsion = 0) :
    IsTorsionFree (concreteDerivationEmbedding I M)
      (concreteConn I M cov)  := by sorry

end Connection

end
