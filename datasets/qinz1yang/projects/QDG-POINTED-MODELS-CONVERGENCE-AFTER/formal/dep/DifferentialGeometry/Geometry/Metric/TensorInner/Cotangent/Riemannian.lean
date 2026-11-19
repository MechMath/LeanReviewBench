import dep.DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.Riemannian
import Mathlib.LinearAlgebra.Dual.Basis

namespace DifferentialGeometry
namespace Tensor0SBundle

noncomputable section


open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def cotangentToCLM {x : M} (α : Tensor0SSpace 1 I x) :
    TangentSpace I x →L[Real] Real where
  toFun X := α (fun _ => X)
  map_add' X Y := by
    have h := α.toMultilinearMap.map_update_add (fun _ => 0) 0 X Y
    change α.toMultilinearMap (fun _ => X + Y) =
      α.toMultilinearMap (fun _ => X) + α.toMultilinearMap (fun _ => Y)
    rw [show (fun _ : Fin 1 => X + Y) = Function.update (fun _ => 0) 0 (X + Y) by
      funext i; fin_cases i; simp]
    rw [show (fun _ : Fin 1 => X) = Function.update (fun _ => 0) 0 X by
      funext i; fin_cases i; simp]
    rw [show (fun _ : Fin 1 => Y) = Function.update (fun _ => 0) 0 Y by
      funext i; fin_cases i; simp]
    exact h
  map_smul' c X := by
    have h := α.toMultilinearMap.map_update_smul (fun _ => 0) 0 c X
    change α.toMultilinearMap (fun _ => c • X) = c • α.toMultilinearMap (fun _ => X)
    rw [show (fun _ : Fin 1 => c • X) = Function.update (fun _ => 0) 0 (c • X) by
      funext i; fin_cases i; simp]
    rw [show (fun _ : Fin 1 => X) = Function.update (fun _ => 0) 0 X by
      funext i; fin_cases i; simp]
    exact h
  cont := α.cont.comp (continuous_pi fun _ => continuous_id)

def cotangentToDual {x : M} (α : Tensor0SSpace 1 I x) :
    Module.Dual Real (TangentSpace I x) :=
  (cotangentToCLM (I := I) α).toLinearMap

omit [FiniteDimensional ℝ E] in
@[simp] theorem cotangentToDual_apply {x : M}
    (α : Tensor0SSpace 1 I x) (X : TangentSpace I x) :
    cotangentToDual (I := I) α X = α (fun _ : Fin 1 => X)  := by sorry

def cotangentToDualLinear {x : M} :
    Tensor0SSpace 1 I x →ₗ[Real] Module.Dual Real (TangentSpace I x) where
  toFun := cotangentToDual (I := I)
  map_add' α β := by
    ext X
    rfl
  map_smul' c α := by
    ext X
    rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem cotangentToDualLinear_apply {x : M}
    (α : Tensor0SSpace 1 I x) :
    cotangentToDualLinear (I := I) α = cotangentToDual (I := I) α  := by sorry

omit [FiniteDimensional ℝ E] in
theorem cotangentToDualLinear_injective {x : M} :
    Function.Injective (cotangentToDualLinear (I := I) (x := x))  := by sorry

private noncomputable def tangentDualToCLM {x : M}
    (α : Module.Dual Real (TangentSpace I x)) : TangentSpace I x →L[Real] Real :=
  LinearMap.toContinuousLinearMap α

def dualToCotangent {x : M} (α : Module.Dual Real (TangentSpace I x)) :
    Tensor0SSpace 1 I x :=
  Tensor0SSpace.ofModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    ((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
      (tangentDualToCLM (I := I) α))

@[simp] theorem dualToCotangent_apply {x : M}
    (α : Module.Dual Real (TangentSpace I x)) (X : TangentSpace I x) :
    dualToCotangent (I := I) α (fun _ : Fin 1 => X) = α X  := by sorry

@[simp] theorem cotangentToDual_dualToCotangent {x : M}
    (α : Module.Dual Real (TangentSpace I x)) :
    cotangentToDual (I := I) (dualToCotangent (I := I) α) = α  := by sorry

def cotangentSharpLinear (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 1 I x →ₗ[Real] TangentSpace I x :=
  ((tangentMetricData (I := I) g x).metric.sharp).toLinearMap.comp
    (cotangentToDualLinear (I := I) (x := x))

def cotangentSharp (g : SmoothRiemannianMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) : TangentSpace I x :=
  cotangentSharpLinear (I := I) g x α

@[simp] theorem cotangentSharpLinear_apply
    (g : SmoothRiemannianMetric I M) (x : M) (α : Tensor0SSpace 1 I x) :
    cotangentSharpLinear (I := I) g x α = cotangentSharp (I := I) g x α  := by sorry

theorem cotangentSharpLinear_injective
    (g : SmoothRiemannianMetric I M) (x : M) :
    Function.Injective (cotangentSharpLinear (I := I) g x)  := by sorry

def cotangentInner (g : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) : Real :=
  g.inner x
    (cotangentSharpLinear (I := I) g x α)
    (cotangentSharpLinear (I := I) g x β)

@[simp] theorem cotangentInner_eq_sharp
    (g : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    cotangentInner (I := I) g x α β =
      g.inner x (cotangentSharp (I := I) g x α)
        (cotangentSharp (I := I) g x β)  := by sorry

def cotangentFlatLinear (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 1 I x →ₗ[Real] Module.Dual Real (Tensor0SSpace 1 I x) where
  toFun α :=
    { toFun := fun β => cotangentInner (I := I) g x α β
      map_add' := by
        intro β γ
        let S := cotangentSharpLinear (I := I) g x
        have hS : S (β + γ) = S β + S γ := map_add S β γ
        change g.inner x (S α) (S (β + γ)) =
          g.inner x (S α) (S β) + g.inner x (S α) (S γ)
        rw [hS]
        simp
      map_smul' := by
        intro c β
        let S := cotangentSharpLinear (I := I) g x
        have hS : S (c • β) = c • S β := map_smul S c β
        change g.inner x (S α) (S (c • β)) = c * g.inner x (S α) (S β)
        rw [hS]
        simp }
  map_add' α β := by
    ext γ
    let S := cotangentSharpLinear (I := I) g x
    have hS : S (α + β) = S α + S β := map_add S α β
    change g.inner x (S (α + β)) (S γ) =
      g.inner x (S α) (S γ) + g.inner x (S β) (S γ)
    rw [hS]
    simp
  map_smul' c α := by
    ext β
    let S := cotangentSharpLinear (I := I) g x
    have hS : S (c • α) = c • S α := map_smul S c α
    change g.inner x (S (c • α)) (S β) = c * g.inner x (S α) (S β)
    rw [hS]
    simp

@[simp] theorem cotangentFlatLinear_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    cotangentFlatLinear (I := I) g x α β =
      cotangentInner (I := I) g x α β  := by sorry

theorem cotangentFlatLinear_injective
    (g : SmoothRiemannianMetric I M) (x : M) :
    Function.Injective (cotangentFlatLinear (I := I) g x)  := by sorry

def cotangentMetricData (g : SmoothRiemannianMetric I M) (x : M) :
    MetricFiberData (Tensor0SSpace 1 I x) :=
  MetricFiberData.ofFlat
    (cotangentFlatLinear (I := I) g x)
    (cotangentFlatLinear_injective (I := I) g x)
    (by
      intro α β
      change g.inner x
          (cotangentSharpLinear (I := I) g x α)
          (cotangentSharpLinear (I := I) g x β) =
        g.inner x
          (cotangentSharpLinear (I := I) g x β)
          (cotangentSharpLinear (I := I) g x α)
      exact g.symm x _ _)
    (by
      intro α
      by_cases hα : cotangentSharpLinear (I := I) g x α = 0
      · change 0 <=
          g.inner x
            (cotangentSharpLinear (I := I) g x α)
            (cotangentSharpLinear (I := I) g x α)
        rw [hα]
        simp
      · exact le_of_lt (g.pos x (cotangentSharpLinear (I := I) g x α) hα))

theorem cotangentMetricData_inner
    (g : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    (cotangentMetricData (I := I) g x).inner α β =
      cotangentInner (I := I) g x α β  := by sorry

def MetricInverseOnFiniteFrameGram {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (frame : Idx -> TangentSpace I x)
    (gInv : Idx -> Idx -> Real) : Prop :=
  forall i j : Idx,
    (∑ k : Idx, gInv i k * g.inner x (frame k) (frame j)) =
        (if i = j then 1 else 0) ∧
      (∑ k : Idx, g.inner x (frame i) (frame k) * gInv k j) =
        (if i = j then 1 else 0)

def MetricInverseInBasis {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) : Prop :=
  forall i j : Idx,
    (∑ k : Idx, gInv i k * g.inner x (basis k) (basis j)) =
        (if i = j then 1 else 0) ∧
      (∑ k : Idx, g.inner x (basis i) (basis k) * gInv k j) =
        (if i = j then 1 else 0)

theorem cotangentSharp_inner
    (g : SmoothRiemannianMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) (X : TangentSpace I x) :
    g.inner x (cotangentSharp (I := I) g x α) X =
      cotangentToDual (I := I) α X  := by sorry

omit [FiniteDimensional ℝ E] in
theorem eq_of_inner_basis_eq
    {Idx : Type*} [Finite Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    {X Y : TangentSpace I x}
    (h : forall i : Idx, g.inner x X (basis i) = g.inner x Y (basis i)) :
    X = Y  := by sorry

theorem cotangentSharp_eq_sum_inv
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (β : Tensor0SSpace 1 I x) :
    cotangentSharp (I := I) g x β =
      ∑ i : Idx,
        (∑ j : Idx, gInv i j * cotangentToDual (I := I) β (basis j)) •
          basis i  := by sorry

theorem cotangentInner_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (α β : Tensor0SSpace 1 I x) :
    cotangentInner (I := I) g x α β =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * cotangentToDual (I := I) α (basis i) *
          cotangentToDual (I := I) β (basis j)  := by sorry

theorem cotangentMetricData_inner_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (α β : Tensor0SSpace 1 I x) :
    (cotangentMetricData (I := I) g x).inner α β =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * cotangentToDual (I := I) α (basis i) *
          cotangentToDual (I := I) β (basis j)  := by sorry

end

end Tensor0SBundle
end DifferentialGeometry

