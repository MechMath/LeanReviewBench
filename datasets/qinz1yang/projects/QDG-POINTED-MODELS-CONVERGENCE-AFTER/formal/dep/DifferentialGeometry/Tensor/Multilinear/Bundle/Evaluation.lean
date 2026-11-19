import dep.DifferentialGeometry.Tensor.RSTensor.Field
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace TensorMultilinear

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [CompleteSpace 𝕜] in
private theorem compContinuousLinearMap_isEmpty
    {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F₁) 𝕜)
    (g : ∀ _ : Fin 0, F₂ →L[𝕜] F₁) :
    f.compContinuousLinearMap g =
      (ContinuousMultilinearMap.constOfIsEmpty 𝕜 _ (f 0) :
        ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F₂) 𝕜)  := by sorry

omit [CompleteSpace 𝕜] in
theorem trivializationAt_tensor0SBundle_succ_fibre {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace (n + 1) I b) (x₀ b : M) :
    (trivializationAt (Tensor0SModel (n + 1) 𝕜 E)
      (fun x : M => Tensor0SSpace (n + 1) I x) x₀ ⟨b, T b⟩).2 =
    (tensor0SSpaceFiberContinuousLinearEquiv (I := I) (n + 1) b (T b)).compContinuousLinearMap
      (fun _ : Fin (n + 1) => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b)  := by sorry

omit [CompleteSpace 𝕜] in
theorem trivializationAt_tensor0SBundle_zero_fibre
    (T : ∀ b : M, Tensor0SSpace 0 I b) (x₀ b : M) :
    (trivializationAt (Tensor0SModel 0 𝕜 E)
      (fun x : M => Tensor0SSpace 0 I x) x₀ ⟨b, T b⟩).2 =
    (ContinuousMultilinearMap.constOfIsEmpty 𝕜 _ ((T b) 0) :
      ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E) 𝕜)  := by sorry

omit [CompleteSpace 𝕜] in
theorem trivializationAt_homBundle_fibre {n : ℕ}
    (ϕ : ∀ b : M, TangentSpace I b →L[𝕜] Tensor0SSpace n I b) (x₀ b : M) :
    (trivializationAt (E →L[𝕜] Tensor0SModel n 𝕜 E)
      (fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) x₀
      ⟨b, ϕ b⟩).2 =
    ((trivializationAt (Tensor0SModel n 𝕜 E)
      (fun x : M => Tensor0SSpace n I x) x₀).continuousLinearMapAt 𝕜 b).comp
      ((ϕ b).comp
        ((trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b))  := by sorry

omit [CompleteSpace 𝕜] in
theorem tensor0SBundle_linearMapAt_apply_of_mem {n : ℕ} (x₀ b : M)
    (hb : b ∈ (trivializationAt (Tensor0SModel n 𝕜 E)
      (fun x : M => Tensor0SSpace n I x) x₀).baseSet)
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin n => E) 𝕜) (v : Fin n → E) :
    (((trivializationAt (Tensor0SModel n 𝕜 E)
        (fun x : M => Tensor0SSpace n I x) x₀).linearMapAt 𝕜 b)
      ((tensor0SSpaceContinuousLinearEquiv (I := I) n b).symm f)) v =
    f (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) b
      ((trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b (v j)))  := by sorry

omit [CompleteSpace 𝕜] in
private theorem tensor0SBundle_linearMapAt_apply_tensor {n : ℕ} (x₀ b : M)
    (hb : b ∈ (trivializationAt (Tensor0SModel n 𝕜 E)
      (fun x : M => Tensor0SSpace n I x) x₀).baseSet)
    (B : Tensor0SSpace n I b) (v : Fin n → E) :
    (((trivializationAt (Tensor0SModel n 𝕜 E)
        (fun x : M => Tensor0SSpace n I x) x₀).linearMapAt 𝕜 b) B) v =
    Tensor0SSpace.eval B
      (fun j => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b (v j))  := by sorry

@[reducible]
def curriedSection {n : ℕ} (T : ∀ b : M, Tensor0SSpace (n + 1) I b) :
    ∀ b : M, TangentSpace I b →L[𝕜] Tensor0SSpace n I b :=
  fun b => tensor0SCurry (I := I) (M := M) n b (T b)

omit [CompleteSpace 𝕜] in
theorem trivializationAt_homBundle_curriedSection_eq {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace (n + 1) I b) (x₀ b : M)
    (hb : b ∈ (trivializationAt (Tensor0SModel n 𝕜 E)
      (fun x : M => Tensor0SSpace n I x) x₀).baseSet) :
    (trivializationAt (E →L[𝕜] Tensor0SModel n 𝕜 E)
      (fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) x₀
      ⟨b, curriedSection T b⟩).2 =
    continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜
      ((trivializationAt (Tensor0SModel (n + 1) 𝕜 E)
        (fun x : M => Tensor0SSpace (n + 1) I x) x₀ ⟨b, T b⟩).2)  := by sorry

omit [CompleteSpace 𝕜] in
private theorem continuous_curriedSection_of_continuous_section {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace (n + 1) I b)
    (hT : Continuous (fun b : M =>
      TotalSpace.mk' (Tensor0SModel (n + 1) 𝕜 E)
        (E := fun x : M => Tensor0SSpace (n + 1) I x) b (T b))) :
    Continuous (fun b : M =>
      TotalSpace.mk' (E →L[𝕜] Tensor0SModel n 𝕜 E)
        (E := fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) b
        (curriedSection T b))  := by sorry

omit [CompleteSpace 𝕜] in
private theorem contMDiff_curriedSection_of_contMDiff_section {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace (n + 1) I b)
    (hT : ContMDiff I (I.prod 𝓘(𝕜, Tensor0SModel (n + 1) 𝕜 E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel (n + 1) 𝕜 E)
          (E := fun x : M => Tensor0SSpace (n + 1) I x) b (T b))) :
    ContMDiff I (I.prod 𝓘(𝕜, E →L[𝕜] Tensor0SModel n 𝕜 E)) ∞
      (fun b : M =>
        TotalSpace.mk' (E →L[𝕜] Tensor0SModel n 𝕜 E)
          (E := fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) b
          (curriedSection T b))  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem tensor0S_curry_apply_eval {n : ℕ} {b : M}
    (T : Tensor0SSpace (n + 1) I b)
    (v0 : TangentSpace I b) (vs : Fin n → TangentSpace I b) :
    Tensor0SSpace.eval (tensor0SCurry (I := I) (M := M) n b T v0) vs =
    Tensor0SSpace.eval T (Fin.cons v0 vs)  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem tensor0S_curry_toModel_apply {n : ℕ} {b : M}
    (T : Tensor0SSpace (n + 1) I b) (v0 : E) (vs : Fin n → E) :
    Tensor0SSpace.toModel
        (tensor0SCurry (I := I) (M := M) n b T
          ((tangentSpaceModelContinuousLinearEquiv (I := I) b).symm v0)) vs =
      Tensor0SSpace.toModel T (Fin.cons v0 vs)  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem tensor0S_curry_toModel_apply_tangent {n : ℕ} {b : M}
    (T : Tensor0SSpace (n + 1) I b) (v0 : TangentSpace I b) (vs : Fin n → E) :
    Tensor0SSpace.toModel (tensor0SCurry (I := I) (M := M) n b T v0) vs =
      Tensor0SSpace.toModel T
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b v0) vs)  := by sorry

omit [CompleteSpace 𝕜] in
private theorem continuous_section_apply_aux : ∀ (n : ℕ)
    (T : ∀ b : M, Tensor0SSpace n I b)
    (_hT : Continuous (fun b : M =>
      TotalSpace.mk' (Tensor0SModel n 𝕜 E)
        (E := fun x : M => Tensor0SSpace n I x) b (T b)))
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (_hv : ∀ i : Fin n, Continuous (fun b : M =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (v i b))),
    Continuous (fun b : M =>
      Tensor0SSpace.eval (T b) (fun i : Fin n => v i b))
 := by sorry

omit [CompleteSpace 𝕜] in
private theorem trivializationAt_tensor0SBundle_succ_fibre_pt {n : ℕ}
    {b : M} (A : Tensor0SSpace (n + 1) I b) (x₀ : M) :
    (trivializationAt (Tensor0SModel (n + 1) 𝕜 E)
      (fun x : M => Tensor0SSpace (n + 1) I x) x₀ ⟨b, A⟩).2 =
    (tensor0SSpaceFiberContinuousLinearEquiv (I := I) (n + 1) b A).compContinuousLinearMap
      (fun _ : Fin (n + 1) => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b)  := by sorry

omit [CompleteSpace 𝕜] in
private theorem trivializationAt_tensor0SBundle_zero_fibre_pt
    {b : M} (A : Tensor0SSpace 0 I b) (x₀ : M) :
    (trivializationAt (Tensor0SModel 0 𝕜 E)
      (fun x : M => Tensor0SSpace 0 I x) x₀ ⟨b, A⟩).2 =
    (ContinuousMultilinearMap.constOfIsEmpty 𝕜 _ (A 0) :
      ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E) 𝕜)  := by sorry

omit [CompleteSpace 𝕜] in
private theorem trivializationAt_homBundle_fibre_pt {n : ℕ}
    {b : M} (φ : TangentSpace I b →L[𝕜] Tensor0SSpace n I b) (x₀ : M) :
    (trivializationAt (E →L[𝕜] Tensor0SModel n 𝕜 E)
      (fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) x₀
      ⟨b, φ⟩).2 =
    ((trivializationAt (Tensor0SModel n 𝕜 E)
      (fun x : M => Tensor0SSpace n I x) x₀).continuousLinearMapAt 𝕜 b).comp
      (φ.comp ((trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b))  := by sorry

omit [CompleteSpace 𝕜] in
private theorem trivializationAt_homBundle_curry_eq_pt {n : ℕ}
    {b : M} (A : Tensor0SSpace (n + 1) I b) (x₀ : M)
    (hb : b ∈ (trivializationAt (Tensor0SModel n 𝕜 E)
      (fun x : M => Tensor0SSpace n I x) x₀).baseSet) :
    (trivializationAt (E →L[𝕜] Tensor0SModel n 𝕜 E)
      (fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) x₀
      ⟨b, tensor0SCurry (I := I) (M := M) n b A⟩).2 =
    continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜
      ((trivializationAt (Tensor0SModel (n + 1) 𝕜 E)
        (fun x : M => Tensor0SSpace (n + 1) I x) x₀ ⟨b, A⟩).2)  := by sorry

omit [CompleteSpace 𝕜] in
private theorem continuous_curry_of_continuous_base {P : Type*} [TopologicalSpace P]
    {n : ℕ} {b : P → M}
    {T : ∀ p : P, Tensor0SSpace (n + 1) I (b p)}
    (hb : Continuous b)
    (hT : Continuous (fun p : P =>
      TotalSpace.mk' (Tensor0SModel (n + 1) 𝕜 E)
        (E := fun x : M => Tensor0SSpace (n + 1) I x) (b p) (T p))) :
    Continuous (fun p : P =>
      TotalSpace.mk' (E →L[𝕜] Tensor0SModel n 𝕜 E)
        (E := fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) (b p)
        (tensor0SCurry (I := I) (M := M) n (b p) (T p)))  := by sorry

omit [CompleteSpace 𝕜] in
private theorem continuous_section_apply_base_aux {P : Type*} [TopologicalSpace P] :
    ∀ (n : ℕ)
    (b : P → M)
    (_hb : Continuous b)
    (T : ∀ p : P, Tensor0SSpace n I (b p))
    (_hT : Continuous (fun p : P =>
      TotalSpace.mk' (Tensor0SModel n 𝕜 E)
        (E := fun x : M => Tensor0SSpace n I x) (b p) (T p)))
    (v : Fin n → ∀ p : P, TangentSpace I (b p))
    (_hv : ∀ i : Fin n, Continuous (fun p : P =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (b p) (v i p))),
    Continuous (fun p : P =>
      Tensor0SSpace.eval (T p) (fun i : Fin n => v i p))
 := by sorry

private theorem contMDiff_section_apply_aux : ∀ (n : ℕ)
    (T : ∀ b : M, Tensor0SSpace n I b)
    (_hT : ContMDiff I (I.prod 𝓘(𝕜, Tensor0SModel n 𝕜 E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel n 𝕜 E)
          (E := fun x : M => Tensor0SSpace n I x) b (T b)))
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (_hv : ∀ i : Fin n, ContMDiff I (I.prod 𝓘(𝕜, E)) ∞
      (fun b : M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (v i b))),
    ContMDiff I 𝓘(𝕜, 𝕜) ∞
      (fun b : M => Tensor0SSpace.eval (T b) (fun i : Fin n => v i b))
 := by sorry

omit [CompleteSpace 𝕜] in
theorem continuous_section_apply
    {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace n I b)
    (hT : Continuous (fun b : M =>
      TotalSpace.mk' (Tensor0SModel n 𝕜 E)
        (E := fun x : M => Tensor0SSpace n I x) b (T b)))
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (hv : ∀ i : Fin n, Continuous (fun b : M =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (v i b))) :
    Continuous (fun b : M =>
      Tensor0SSpace.eval (T b) (fun i : Fin n => v i b))  := by sorry

omit [CompleteSpace 𝕜] in
theorem continuous_section_apply_base
    {P : Type*} [TopologicalSpace P] {n : ℕ}
    (b : P → M) (hb : Continuous b)
    (T : ∀ p : P, Tensor0SSpace n I (b p))
    (hT : Continuous (fun p : P =>
      TotalSpace.mk' (Tensor0SModel n 𝕜 E)
        (E := fun x : M => Tensor0SSpace n I x) (b p) (T p)))
    (v : Fin n → ∀ p : P, TangentSpace I (b p))
    (hv : ∀ i : Fin n, Continuous (fun p : P =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (b p) (v i p))) :
    Continuous (fun p : P =>
      Tensor0SSpace.eval (T p) (fun i : Fin n => v i p))  := by sorry

omit [CompleteSpace 𝕜] in
private theorem
    contMDiffWithinAt_curriedSection_of_contMDiffWithinAt_section_base
    {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
    {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners 𝕜 EP HP}
    {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
    {n : ℕ} {s : Set P} {p₀ : P}
    (b : P → M) (hb : ContMDiffWithinAt IP I ∞ b s p₀)
    (T : ∀ p : P, Tensor0SSpace (n + 1) I (b p))
    (hT : ContMDiffWithinAt IP (I.prod 𝓘(𝕜, Tensor0SModel (n + 1) 𝕜 E)) ∞
      (fun p : P => TotalSpace.mk' (Tensor0SModel (n + 1) 𝕜 E)
        (E := fun x : M => Tensor0SSpace (n + 1) I x) (b p) (T p)) s p₀) :
    ContMDiffWithinAt IP (I.prod 𝓘(𝕜, E →L[𝕜] Tensor0SModel n 𝕜 E)) ∞
      (fun p : P => TotalSpace.mk' (E →L[𝕜] Tensor0SModel n 𝕜 E)
        (E := fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) (b p)
        (tensor0SCurry (I := I) (M := M) n (b p) (T p))) s p₀  := by sorry

theorem contMDiffWithinAt_section_apply_base
    {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
    {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners 𝕜 EP HP}
    {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] :
    ∀ (n : ℕ) {s : Set P} {p₀ : P}
    (b : P → M)
    (_hb : ContMDiffWithinAt IP I ∞ b s p₀)
    (T : ∀ p : P, Tensor0SSpace n I (b p))
    (_hT : ContMDiffWithinAt IP (I.prod 𝓘(𝕜, Tensor0SModel n 𝕜 E)) ∞
      (fun p : P => TotalSpace.mk' (Tensor0SModel n 𝕜 E)
        (E := fun x : M => Tensor0SSpace n I x) (b p) (T p)) s p₀)
    (v : Fin n → ∀ p : P, TangentSpace I (b p))
    (_hv : ∀ i, ContMDiffWithinAt IP (I.prod 𝓘(𝕜, E)) ∞
      (fun p : P => TotalSpace.mk' E
        (E := fun x : M => TangentSpace I x) (b p) (v i p)) s p₀),
    ContMDiffWithinAt IP 𝓘(𝕜, 𝕜) ∞
      (fun p : P => Tensor0SSpace.eval (T p) (fun i => v i p)) s p₀
 := by sorry

theorem contMDiff_section_apply
    {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace n I b)
    (hT : ContMDiff I (I.prod 𝓘(𝕜, Tensor0SModel n 𝕜 E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel n 𝕜 E)
          (E := fun x : M => Tensor0SSpace n I x) b (T b)))
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (hv : ∀ i : Fin n, ContMDiff I (I.prod 𝓘(𝕜, E)) ∞
      (fun b : M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (v i b))) :
    ContMDiff I 𝓘(𝕜, 𝕜) ∞
      (fun b : M => Tensor0SSpace.eval (T b) (fun i : Fin n => v i b))  := by sorry

theorem contMDiff_tensor0SField_apply
    {n : ℕ}
    (T : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) n)
    (v : Fin n → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    ContMDiff I 𝓘(𝕜, 𝕜) ∞
      (fun b : M => T b (fun i : Fin n => v i b))  := by sorry

omit [CompleteSpace 𝕜] in
theorem contMDiffAt_curriedSection_of_contMDiffAt_section {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace (n + 1) I b) (x₀ : M)
    (hT : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel (n + 1) 𝕜 E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel (n + 1) 𝕜 E)
          (E := fun x : M => Tensor0SSpace (n + 1) I x) b (T b)) x₀) :
    ContMDiffAt I (I.prod 𝓘(𝕜, E →L[𝕜] Tensor0SModel n 𝕜 E)) ∞
      (fun b : M =>
        TotalSpace.mk' (E →L[𝕜] Tensor0SModel n 𝕜 E)
          (E := fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) b
          (curriedSection T b)) x₀  := by sorry

private theorem contMDiffAt_section_apply_aux : ∀ (n : ℕ) (x₀ : M)
    (T : ∀ b : M, Tensor0SSpace n I b)
    (_hT : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel n 𝕜 E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel n 𝕜 E)
          (E := fun x : M => Tensor0SSpace n I x) b (T b)) x₀)
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (_hv : ∀ i : Fin n, ContMDiffAt I (I.prod 𝓘(𝕜, E)) ∞
      (fun b : M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (v i b)) x₀),
    ContMDiffAt I 𝓘(𝕜, 𝕜) ∞
      (fun b : M => Tensor0SSpace.eval (T b) (fun i : Fin n => v i b)) x₀
 := by sorry

theorem contMDiffAt_section_apply
    {n : ℕ} {x₀ : M}
    (T : ∀ b : M, Tensor0SSpace n I b)
    (hT : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel n 𝕜 E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel n 𝕜 E)
          (E := fun x : M => Tensor0SSpace n I x) b (T b)) x₀)
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (hv : ∀ i : Fin n, ContMDiffAt I (I.prod 𝓘(𝕜, E)) ∞
      (fun b : M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (v i b)) x₀) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) ∞
      (fun b : M => Tensor0SSpace.eval (T b) (fun i : Fin n => v i b)) x₀  := by sorry

omit [CompleteSpace 𝕜] in
theorem contMDiffAt_curriedSection_of_contMDiffAt_section_one {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace (n + 1) I b) (x₀ : M)
    (hT : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel (n + 1) 𝕜 E))
      (1 : WithTop ℕ∞)
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel (n + 1) 𝕜 E)
          (E := fun x : M => Tensor0SSpace (n + 1) I x) b (T b)) x₀) :
    ContMDiffAt I (I.prod 𝓘(𝕜, E →L[𝕜] Tensor0SModel n 𝕜 E))
      (1 : WithTop ℕ∞)
      (fun b : M =>
        TotalSpace.mk' (E →L[𝕜] Tensor0SModel n 𝕜 E)
          (E := fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) b
          (curriedSection T b)) x₀  := by sorry

private theorem contMDiffAt_section_apply_one_aux : ∀ (n : ℕ) (x₀ : M)
    (T : ∀ b : M, Tensor0SSpace n I b)
    (_hT : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel n 𝕜 E))
      (1 : WithTop ℕ∞)
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel n 𝕜 E)
          (E := fun x : M => Tensor0SSpace n I x) b (T b)) x₀)
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (_hv : ∀ i : Fin n, ContMDiffAt I (I.prod 𝓘(𝕜, E))
      (1 : WithTop ℕ∞)
      (fun b : M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (v i b)) x₀),
    ContMDiffAt I 𝓘(𝕜, 𝕜) (1 : WithTop ℕ∞)
      (fun b : M => Tensor0SSpace.eval (T b) (fun i : Fin n => v i b)) x₀
 := by sorry

theorem contMDiffAt_section_apply_one
    {n : ℕ} {x₀ : M}
    (T : ∀ b : M, Tensor0SSpace n I b)
    (hT : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel n 𝕜 E))
      (1 : WithTop ℕ∞)
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel n 𝕜 E)
          (E := fun x : M => Tensor0SSpace n I x) b (T b)) x₀)
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (hv : ∀ i : Fin n, ContMDiffAt I (I.prod 𝓘(𝕜, E))
      (1 : WithTop ℕ∞)
      (fun b : M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (v i b)) x₀) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (1 : WithTop ℕ∞)
      (fun b : M => Tensor0SSpace.eval (T b) (fun i : Fin n => v i b)) x₀  := by sorry

theorem contMDiffWithinAt_section_apply_prod (n : ℕ)
    {s : Set (M × 𝕜)} {p₀ : M × 𝕜}
    (T : ∀ b : M, Tensor0SSpace n I b)
    (hT : ContMDiffWithinAt (I.prod 𝓘(𝕜, 𝕜))
      (I.prod 𝓘(𝕜, Tensor0SModel n 𝕜 E)) ∞
      (fun p : M × 𝕜 => TotalSpace.mk' (Tensor0SModel n 𝕜 E)
        (E := fun x : M => Tensor0SSpace n I x) p.1 (T p.1)) s p₀)
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (hv : ∀ i, ContMDiffWithinAt (I.prod 𝓘(𝕜, 𝕜)) (I.prod 𝓘(𝕜, E)) ∞
      (fun p : M × 𝕜 => TotalSpace.mk' E
        (E := fun x : M => TangentSpace I x) p.1 (v i p.1)) s p₀) :
    ContMDiffWithinAt (I.prod 𝓘(𝕜, 𝕜)) 𝓘(𝕜, 𝕜) ∞
      (fun p : M × 𝕜 => Tensor0SSpace.eval (T p.1) (fun i => v i p.1)) s p₀  := by sorry

theorem contMDiffAt_section_apply_prod {n : ℕ} {p₀ : M × 𝕜}
    (T : ∀ b : M, Tensor0SSpace n I b)
    (hT : ContMDiffAt (I.prod 𝓘(𝕜, 𝕜))
      (I.prod 𝓘(𝕜, Tensor0SModel n 𝕜 E)) ∞
      (fun p : M × 𝕜 => TotalSpace.mk' (Tensor0SModel n 𝕜 E)
        (E := fun x : M => Tensor0SSpace n I x) p.1 (T p.1)) p₀)
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (hv : ∀ i, ContMDiffAt (I.prod 𝓘(𝕜, 𝕜)) (I.prod 𝓘(𝕜, E)) ∞
      (fun p : M × 𝕜 => TotalSpace.mk' E
        (E := fun x : M => TangentSpace I x) p.1 (v i p.1)) p₀) :
    ContMDiffAt (I.prod 𝓘(𝕜, 𝕜)) 𝓘(𝕜, 𝕜) ∞
      (fun p : M × 𝕜 => Tensor0SSpace.eval (T p.1) (fun i => v i p.1)) p₀  := by sorry

theorem contMDiff_section_apply_prod {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace n I b)
    (hT : ContMDiff (I.prod 𝓘(𝕜, 𝕜))
      (I.prod 𝓘(𝕜, Tensor0SModel n 𝕜 E)) ∞
      (fun p : M × 𝕜 => TotalSpace.mk' (Tensor0SModel n 𝕜 E)
        (E := fun x : M => Tensor0SSpace n I x) p.1 (T p.1)))
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (hv : ∀ i, ContMDiff (I.prod 𝓘(𝕜, 𝕜)) (I.prod 𝓘(𝕜, E)) ∞
      (fun p : M × 𝕜 => TotalSpace.mk' E
        (E := fun x : M => TangentSpace I x) p.1 (v i p.1))) :
    ContMDiff (I.prod 𝓘(𝕜, 𝕜)) 𝓘(𝕜, 𝕜) ∞
      (fun p : M × 𝕜 => Tensor0SSpace.eval (T p.1) (fun i => v i p.1))  := by sorry

end TensorMultilinear

end DifferentialGeometry
end

