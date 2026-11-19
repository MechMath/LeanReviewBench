import dep.DifferentialGeometry.Geometry.Metric.MetricFiberData.Hom
import dep.DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric
import dep.DifferentialGeometry.Tensor.RSTensor.Algebra.Product

set_option autoImplicit false

namespace DifferentialGeometry
namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem sum_fin_two_fun {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α]
    (F : (Fin 2 -> Idx) -> α) :
    (∑ I0 : Fin 2 -> Idx, F I0) =
      ∑ i : Idx, ∑ j : Idx, F (fun a : Fin 2 => if a = 0 then i else j)  := by sorry

theorem sum_fin_succ_fun {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α] (s : Nat)
    (F : (Fin (s + 1) -> Idx) -> α) :
    (∑ I0 : Fin (s + 1) -> Idx, F I0) =
      ∑ i : Idx, ∑ tail : Fin s -> Idx, F (Fin.cons i tail)  := by sorry

theorem sum_fin_one_fun {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α]
    (F : (Fin 1 -> Idx) -> α) :
    (∑ I0 : Fin 1 -> Idx, F I0) =
      ∑ i : Idx, F (fun _ : Fin 1 => i)  := by sorry

omit [FiniteDimensional ℝ E] in
theorem basis_repr_eq_sum_inv_inner
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Z : TangentSpace I x) (i : Idx) :
    basis.repr Z i =
      ∑ j : Idx, gInv i j * g.inner x Z (basis j)  := by sorry

omit [FiniteDimensional ℝ E] in
theorem linearMap_trace_eq_sum_inv_inner_apply
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A : TangentSpace I x →ₗ[Real] TangentSpace I x) :
    LinearMap.trace Real (TangentSpace I x) A =
      ∑ i : Idx, ∑ j : Idx, gInv i j * g.inner x (A (basis i)) (basis j)  := by sorry

theorem linearMap_trace_nonneg_of_metric_inner_apply_self_nonneg
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : TangentSpace I x →ₗ[Real] TangentSpace I x)
    (hA : ∀ v : TangentSpace I x, 0 <= g.inner x (A v) v) :
    0 <= LinearMap.trace Real (TangentSpace I x) A  := by sorry

theorem hom_normSq_eq_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {W : Type*} [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (D : MetricFiberData W)
    (A : TangentSpace I x →ₗ[Real] W) :
    MetricFiberData.homFlatLinear (tangentMetricData (I := I) g x).metric D A A =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * D.inner (A (basis i)) (A (basis j))  := by sorry

theorem hom_inner_eq_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {W : Type*} [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (D : MetricFiberData W)
    (A B : TangentSpace I x →ₗ[Real] W) :
    MetricFiberData.homFlatLinear (tangentMetricData (I := I) g x).metric D A B =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * D.inner (A (basis i)) (B (basis j))  := by sorry

theorem homCLM_normSq_eq_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {W : Type*} [AddCommGroup W] [Module Real W] [TopologicalSpace W]
    (hTopAdd : IsTopologicalAddGroup W) (hContSMul : ContinuousSMul Real W)
    [FiniteDimensional Real W]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (D : MetricFiberData W)
    (A : TangentSpace I x →L[Real] W) :
    (@MetricFiberData.homCLM
      (TangentSpace I x) W
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance
      inferInstance inferInstance inferInstance hTopAdd hContSMul inferInstance
      (tangentMetricData (I := I) g x).metric D).flat A A =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * D.inner (A (basis i)) (A (basis j))  := by sorry

theorem homCLM_inner_eq_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {W : Type*} [AddCommGroup W] [Module Real W] [TopologicalSpace W]
    (hTopAdd : IsTopologicalAddGroup W) (hContSMul : ContinuousSMul Real W)
    [FiniteDimensional Real W]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (D : MetricFiberData W)
    (A B : TangentSpace I x →L[Real] W) :
    (@MetricFiberData.homCLM
      (TangentSpace I x) W
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance
      inferInstance inferInstance inferInstance hTopAdd hContSMul inferInstance
      (tangentMetricData (I := I) g x).metric D).flat A B =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * D.inner (A (basis i)) (B (basis j))  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem tensor0S_curry_one_apply
    [IsManifold I 1 M]
    {x : M} (A : Tensor0SSpace 2 I x)
    (X Y : TangentSpace I x) :
    (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x A X)
        (fun _ : Fin 1 => Y) =
      A (fun a : Fin 2 => if a = 0 then X else Y)  := by sorry

omit [FiniteDimensional ℝ E] in
theorem tensor0S_curry_apply_cons
    {x : M} (s : Nat) (A : Tensor0SSpace (s + 1) I x)
    (X : TangentSpace I x) (tail : Fin s -> TangentSpace I x) :
    (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x A X) tail =
      A (Fin.cons X tail)  := by sorry

omit [FiniteDimensional ℝ E] in
theorem coordInner0S_zero_eq
    {Idx : Type*} [Fintype Idx] {x : M}
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace 0 I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) 0 gInv A B basis =
      A Fin.elim0 * B Fin.elim0  := by sorry

omit [FiniteDimensional ℝ E] in
theorem coordInner0S_one_eq
    {Idx : Type*} [Fintype Idx] {x : M}
    (gInv : Idx -> Idx -> Real)
    (α β : Tensor0SSpace 1 I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) 1 gInv α β basis =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * cotangentToDual (I := I) α (basis i) *
          cotangentToDual (I := I) β (basis j)  := by sorry

omit [FiniteDimensional ℝ E] in
theorem coordInner0S_succ_summand_eq
    {Idx : Type*} {x : M} (s : Nat)
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace (s + 1) I x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (i j : Idx) (tailI tailJ : Fin s -> Idx) :
    ((∏ a : Fin (s + 1),
        gInv (((Fin.cons i tailI : Fin (s + 1) -> Idx) a))
          (((Fin.cons j tailJ : Fin (s + 1) -> Idx) a))) *
        A (fun a : Fin (s + 1) =>
          basis (((Fin.cons i tailI : Fin (s + 1) -> Idx) a)))) *
      B (fun a : Fin (s + 1) =>
        basis (((Fin.cons j tailJ : Fin (s + 1) -> Idx) a))) =
      (gInv i j * (∏ a : Fin s, gInv (tailI a) (tailJ a)) *
          ((tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x A) (basis i))
            (fun a : Fin s => basis (tailI a))) *
        ((tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x B) (basis j))
          (fun a : Fin s => basis (tailJ a))  := by sorry

omit [FiniteDimensional ℝ E] in
theorem coordInner0S_succ_eq
    {Idx : Type*} [Fintype Idx] {x : M} (s : Nat)
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace (s + 1) I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) (s + 1) gInv A B basis =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          coordInner0S (I := I) (x := x) s gInv
            ((tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x A) (basis i))
            ((tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x B) (basis j))
            basis  := by sorry

omit [FiniteDimensional ℝ E] in
theorem coordInner0S_smul_smul
    {Idx : Type*} [Fintype Idx] {x : M} (s : Nat)
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (c d : Real) :
    coordInner0S (I := I) (x := x) s gInv (c • A) (d • B) basis =
      c * d * coordInner0S (I := I) (x := x) s gInv A B basis  := by sorry

omit [FiniteDimensional ℝ E] in
theorem coordInner0S_smul_right
    {Idx : Type*} [Fintype Idx] {x : M} (s : Nat)
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (c : Real) :
    coordInner0S (I := I) (x := x) s gInv A (c • B) basis =
      c * coordInner0S (I := I) (x := x) s gInv A B basis  := by sorry

omit [FiniteDimensional ℝ E] in
theorem coordInner0S_smul_left
    {Idx : Type*} [Fintype Idx] {x : M} (s : Nat)
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (c : Real) :
    coordInner0S (I := I) (x := x) s gInv (c • A) B basis =
      c * coordInner0S (I := I) (x := x) s gInv A B basis  := by sorry

omit [FiniteDimensional ℝ E] in
theorem coordInner0S_zero_left
    {Idx : Type*} [Fintype Idx] {x : M} (s : Nat)
    (gInv : Idx -> Idx -> Real)
    (B : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) s gInv 0 B basis = 0  := by sorry

omit [FiniteDimensional ℝ E] in
theorem coordInner0S_add_left
    {Idx : Type*} [Fintype Idx] {x : M} (s : Nat)
    (gInv : Idx -> Idx -> Real)
    (A B C : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) s gInv (A + B) C basis =
      coordInner0S (I := I) (x := x) s gInv A C basis +
        coordInner0S (I := I) (x := x) s gInv B C basis  := by sorry

omit [FiniteDimensional ℝ E] in
theorem coordInner0S_sum_left
    {Idx ι : Type*} [Fintype Idx] [Fintype ι] {x : M} (s : Nat)
    (gInv : Idx -> Idx -> Real)
    (A : ι -> Tensor0SSpace s I x) (B : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (c : ι -> Real) :
    coordInner0S (I := I) (x := x) s gInv
        (∑ i : ι, c i • A i) B basis =
      ∑ i : ι, c i *
        coordInner0S (I := I) (x := x) s gInv (A i) B basis  := by sorry

omit [FiniteDimensional ℝ E] in
theorem tensor0S_curry_product_one_two
    {x : M}
    (α : Tensor0SSpace 1 I x) (A : Tensor0SSpace 2 I x)
    (X : TangentSpace I x) :
    (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 2 x
        (Tensor0SSpace.product (r := 1) (s := 2) α A) X) =
      α (fun _ : Fin 1 => X) • A  := by sorry

end

end Tensor0SBundle
end DifferentialGeometry

