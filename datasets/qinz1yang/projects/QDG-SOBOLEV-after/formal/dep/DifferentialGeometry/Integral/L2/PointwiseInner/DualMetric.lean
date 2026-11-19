import dep.DifferentialGeometry.Integral.Measure.ChartDensity
import dep.DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.Algebra.BigOperators.Ring.Finset



noncomputable section

open Manifold Set Filter Bundle Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace L2

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]




def modelInnerAt
    (g : SmoothRiemannianMetric I M) (x : M) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  g.inner x

@[simp] lemma modelInnerAt_apply
    (g : SmoothRiemannianMetric I M) (x : M) (v w : E) :
    modelInnerAt (I := I) (M := M) g x v w = g.inner x v w  := by sorry

lemma modelInnerAt_symm
    (g : SmoothRiemannianMetric I M) (x : M) (v w : E) :
    modelInnerAt (I := I) (M := M) g x v w =
      modelInnerAt (I := I) (M := M) g x w v  := by sorry

lemma modelInnerAt_pos_of_ne_zero
    (g : SmoothRiemannianMetric I M) (x : M)
    {v : E} (hv : v ≠ 0) :
    0 < modelInnerAt (I := I) (M := M) g x v v  := by sorry

lemma modelInnerAt_nonneg
    (g : SmoothRiemannianMetric I M) (x : M) (v : E) :
    0 ≤ modelInnerAt (I := I) (M := M) g x v v  := by sorry

lemma modelInnerAt_eq_zero_iff
    (g : SmoothRiemannianMetric I M) (x : M) (v : E) :
    modelInnerAt (I := I) (M := M) g x v v = 0 ↔ v = 0  := by sorry

def gramMatrixAt (g : SmoothRiemannianMetric I M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j =>
    g.inner x ((chartModelBasis E) i) ((chartModelBasis E) j)

@[simp] lemma gramMatrixAt_apply (g : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    gramMatrixAt (I := I) (M := M) g x i j =
      g.inner x ((chartModelBasis E) i) ((chartModelBasis E) j)  := by sorry

lemma gramMatrixAt_isHermitian
    (g : SmoothRiemannianMetric I M) (x : M) :
    (gramMatrixAt (I := I) (M := M) g x).IsHermitian  := by sorry

lemma gramMatrixAt_inv_isHermitian
    (g : SmoothRiemannianMetric I M) (x : M) :
    ((gramMatrixAt (I := I) (M := M) g x)⁻¹).IsHermitian  := by sorry

lemma gramMatrixAt_posDef
    (g : SmoothRiemannianMetric I M) (x : M) :
    (gramMatrixAt (I := I) (M := M) g x).PosDef  := by sorry

lemma gramMatrixAt_inv_posSemidef
    (g : SmoothRiemannianMetric I M) (x : M) :
    ((gramMatrixAt (I := I) (M := M) g x)⁻¹).PosSemidef  := by sorry

lemma gramMatrixAt_inv_eigenvalues_pos
    (g : SmoothRiemannianMetric I M) (x : M) (k : Fin (Module.finrank ℝ E)) :
    0 < (gramMatrixAt_inv_isHermitian (I := I) (M := M) g x).eigenvalues k  := by sorry

lemma gramMatrixAt_isUnit
    (g : SmoothRiemannianMetric I M) (x : M) :
    IsUnit (gramMatrixAt (I := I) (M := M) g x)  := by sorry

lemma gramMatrixAt_inv_mul_self
    (g : SmoothRiemannianMetric I M) (x : M) :
    (gramMatrixAt (I := I) (M := M) g x)⁻¹ *
        gramMatrixAt (I := I) (M := M) g x = 1  := by sorry

noncomputable def separableFormAt
    (g : SmoothRiemannianMetric I M) (x : M) (r : ℕ) (v : Fin r → E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
    (fun i => g.inner x (v i))

@[simp]
lemma separableFormAt_apply
    (g : SmoothRiemannianMetric I M) (x : M) (r : ℕ) (v w : Fin r → E) :
    separableFormAt (I := I) (M := M) g x r v w =
      ∏ i : Fin r, g.inner x (v i) (w i)  := by sorry

private noncomputable def lowerAllUpperIndicesFn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E) (v : Fin (r + s) → E) : ℝ :=
  T (separableFormAt (I := I) (M := M) g x r
      (fun i : Fin r => v (Fin.castAdd s i)))
    (fun j : Fin s => v (Fin.natAdd r j))


private lemma castAdd_ne_natAdd {r s : ℕ} (i : Fin r) (j : Fin s) :
    Fin.castAdd s i ≠ Fin.natAdd r j  := by sorry

private lemma natAdd_ne_castAdd {r s : ℕ} (j : Fin s) (i : Fin r) :
    Fin.natAdd r j ≠ Fin.castAdd s i  := by sorry

private lemma update_castAdd_first
    {r s : ℕ} (v : Fin (r + s) → E) (i : Fin r) (c : E) :
    (fun k : Fin r => Function.update v (Fin.castAdd s i) c (Fin.castAdd s k)) =
      Function.update (fun k : Fin r => v (Fin.castAdd s k)) i c  := by sorry

private lemma update_castAdd_first_noop_last
    {r s : ℕ} (v : Fin (r + s) → E) (i : Fin r) (c : E) :
    (fun j : Fin s => Function.update v (Fin.castAdd s i) c (Fin.natAdd r j)) =
      (fun j : Fin s => v (Fin.natAdd r j))  := by sorry

private lemma update_natAdd_last_noop_first
    {r s : ℕ} (v : Fin (r + s) → E) (j : Fin s) (c : E) :
    (fun k : Fin r => Function.update v (Fin.natAdd r j) c (Fin.castAdd s k)) =
      (fun k : Fin r => v (Fin.castAdd s k))  := by sorry

private lemma update_natAdd_last
    {r s : ℕ} (v : Fin (r + s) → E) (j : Fin s) (c : E) :
    (fun k : Fin s => Function.update v (Fin.natAdd r j) c (Fin.natAdd r k)) =
      Function.update (fun k : Fin s => v (Fin.natAdd r k)) j c  := by sorry

private lemma separableFormAt_update_add
    (g : SmoothRiemannianMetric I M) (x : M) (r : ℕ)
    (v : Fin r → E) (i : Fin r) (a b : E) :
    separableFormAt (I := I) (M := M) g x r
        (Function.update v i (a + b))
      = separableFormAt (I := I) (M := M) g x r (Function.update v i a) +
        separableFormAt (I := I) (M := M) g x r (Function.update v i b)  := by sorry

private lemma separableFormAt_update_smul
    (g : SmoothRiemannianMetric I M) (x : M) (r : ℕ)
    (v : Fin r → E) (i : Fin r) (c : ℝ) (a : E) :
    separableFormAt (I := I) (M := M) g x r
        (Function.update v i (c • a))
      = c • separableFormAt (I := I) (M := M) g x r (Function.update v i a)  := by sorry

private noncomputable def lowerAllUpperIndicesML
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E) :
    MultilinearMap ℝ (fun _ : Fin (r + s) => E) ℝ := by
  classical
  refine MultilinearMap.mk'
    (fun v => lowerAllUpperIndicesFn (I := I) (M := M) g r s x T v)
    (fun v i a b => ?_) (fun v i c a => ?_)
  · 
    refine Fin.addCases ?_ ?_ i
    · intro i'
      simp only [lowerAllUpperIndicesFn]
      rw [update_castAdd_first_noop_last,
          update_castAdd_first_noop_last,
          update_castAdd_first_noop_last,
          update_castAdd_first,
          update_castAdd_first,
          update_castAdd_first]
      rw [separableFormAt_update_add,
          ContinuousLinearMap.map_add,
          ContinuousMultilinearMap.add_apply]
    · intro j'
      simp only [lowerAllUpperIndicesFn]
      rw [update_natAdd_last_noop_first,
          update_natAdd_last_noop_first,
          update_natAdd_last_noop_first,
          update_natAdd_last,
          update_natAdd_last,
          update_natAdd_last]
      rw [ContinuousMultilinearMap.map_update_add]
  · 
    refine Fin.addCases ?_ ?_ i
    · intro i'
      simp only [lowerAllUpperIndicesFn]
      rw [update_castAdd_first_noop_last,
          update_castAdd_first_noop_last,
          update_castAdd_first,
          update_castAdd_first]
      rw [separableFormAt_update_smul,
          ContinuousLinearMap.map_smul,
          ContinuousMultilinearMap.smul_apply]
    · intro j'
      simp only [lowerAllUpperIndicesFn]
      rw [update_natAdd_last_noop_first,
          update_natAdd_last_noop_first,
          update_natAdd_last,
          update_natAdd_last]
      rw [ContinuousMultilinearMap.map_update_smul]


@[simp]
private lemma lowerAllUpperIndicesML_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E) (v : Fin (r + s) → E) :
    lowerAllUpperIndicesML (I := I) (M := M) g r s x T v =
      T (separableFormAt (I := I) (M := M) g x r
          (fun i : Fin r => v (Fin.castAdd s i)))
        (fun j : Fin s => v (Fin.natAdd r j))  := by sorry

private lemma lowerAllUpperIndicesML_norm_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E) (v : Fin (r + s) → E) :
    ‖lowerAllUpperIndicesML (I := I) (M := M) g r s x T v‖
      ≤ (‖T‖ * ∏ _i : Fin r, ‖modelInnerAt (I := I) (M := M) g x‖) *
        ∏ j : Fin (r + s), ‖v j‖  := by sorry

private noncomputable def lowerAllUpperIndicesCMLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (r + s) => E) ℝ :=
  (lowerAllUpperIndicesML (I := I) (M := M) g r s x T).mkContinuous
    (‖T‖ * ∏ _i : Fin r, ‖modelInnerAt (I := I) (M := M) g x‖)
    (lowerAllUpperIndicesML_norm_bound (I := I) (M := M) g r s x T)

@[simp]
private lemma lowerAllUpperIndicesCMLM_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E) (v : Fin (r + s) → E) :
    lowerAllUpperIndicesCMLM (I := I) (M := M) g r s x T v =
      T (separableFormAt (I := I) (M := M) g x r
          (fun i : Fin r => v (Fin.castAdd s i)))
        (fun j : Fin s => v (Fin.natAdd r j))  := by sorry

private lemma lowerAllUpperIndicesCMLM_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    lowerAllUpperIndicesCMLM (I := I) (M := M) g r s x 0 = 0  := by sorry

private lemma lowerAllUpperIndicesCMLM_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T₁ T₂ : TensorRSModel r s ℝ E) :
    lowerAllUpperIndicesCMLM (I := I) (M := M) g r s x (T₁ + T₂) =
      lowerAllUpperIndicesCMLM (I := I) (M := M) g r s x T₁ +
        lowerAllUpperIndicesCMLM (I := I) (M := M) g r s x T₂  := by sorry

private lemma lowerAllUpperIndicesCMLM_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (T : TensorRSModel r s ℝ E) :
    lowerAllUpperIndicesCMLM (I := I) (M := M) g r s x (c • T) =
      c • lowerAllUpperIndicesCMLM (I := I) (M := M) g r s x T  := by sorry

private noncomputable def lowerAllUpperIndicesAddHom
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) →+
      ContinuousMultilinearMap ℝ (fun _ : Fin (r + s) => E) ℝ where
  toFun := fun T => lowerAllUpperIndicesCMLM (I := I) (M := M) g r s x T
  map_zero' := lowerAllUpperIndicesCMLM_zero
    (I := I) (M := M) g r s x
  map_add' := fun T₁ T₂ =>
    lowerAllUpperIndicesCMLM_add (I := I) (M := M) g r s x T₁ T₂


private lemma lowerAllUpperIndicesCMLM_norm_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E) :
    ‖lowerAllUpperIndicesCMLM (I := I) (M := M) g r s x T‖
      ≤ (∏ _i : Fin r, ‖modelInnerAt (I := I) (M := M) g x‖) * ‖T‖  := by sorry

noncomputable def lowerAllUpperIndices
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin (r + s) => E) ℝ where
  toFun := fun T => lowerAllUpperIndicesCMLM (I := I) (M := M) g r s x T
  map_add' := lowerAllUpperIndicesCMLM_add (I := I) (M := M) g r s x
  map_smul' := lowerAllUpperIndicesCMLM_smul (I := I) (M := M) g r s x
  cont := AddMonoidHomClass.continuous_of_bound
    (lowerAllUpperIndicesAddHom (I := I) (M := M) g r s x)
    (∏ i : Fin r, ‖modelInnerAt (I := I) (M := M) g x‖) (fun T =>
      (lowerAllUpperIndicesCMLM_norm_bound
        (I := I) (M := M) g r s x T).trans_eq (by ring))


@[simp]
lemma lowerAllUpperIndices_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E) (v : Fin (r + s) → E) :
    lowerAllUpperIndices (I := I) (M := M) g r s x T v =
      T (separableFormAt (I := I) (M := M) g x r
          (fun i : Fin r => v (Fin.castAdd s i)))
        (fun j : Fin s => v (Fin.natAdd r j))  := by sorry

private lemma separableFormAt_basis_apply
    (g : SmoothRiemannianMetric I M) (x : M) (r : ℕ)
    (idx jdx : Fin r → Fin (Module.finrank ℝ E)) :
    separableFormAt (I := I) (M := M) g x r
        (fun k : Fin r => (chartModelBasis E) (idx k))
        (fun k : Fin r => (chartModelBasis E) (jdx k)) =
      ∏ k : Fin r,
        gramMatrixAt (I := I) (M := M) g x (idx k) (jdx k)  := by sorry

private lemma lower_at_basis_pair_zero_of_lower_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E)
    (hT : lowerAllUpperIndices (I := I) (M := M) g r s x T = 0)
    (idx : Fin r → Fin (Module.finrank ℝ E))
    (jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (T (separableFormAt (I := I) (M := M) g x r
          (fun k : Fin r => (chartModelBasis E) (idx k))))
        (fun j : Fin s => (chartModelBasis E) (jdx j)) = 0  := by sorry

private lemma cmlm_eq_zero_of_basis_zero
    {p : ℕ} (S : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) ℝ)
    (h : ∀ φ : Fin p → Fin (Module.finrank ℝ E),
      S (fun k : Fin p => (chartModelBasis E) (φ k)) = 0) :
    S = 0  := by sorry

private lemma tensor0SModel_ext_basis
    {p : ℕ} (S₁ S₂ : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) ℝ)
    (h : ∀ φ : Fin p → Fin (Module.finrank ℝ E),
      S₁ (fun k : Fin p => (chartModelBasis E) (φ k)) =
        S₂ (fun k : Fin p => (chartModelBasis E) (φ k))) :
    S₁ = S₂  := by sorry

theorem lowerAllUpperIndices_injective
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    Function.Injective
      (lowerAllUpperIndices (I := I) (M := M) g r s x)  := by sorry

end L2
end Integral
end DifferentialGeometry

end
