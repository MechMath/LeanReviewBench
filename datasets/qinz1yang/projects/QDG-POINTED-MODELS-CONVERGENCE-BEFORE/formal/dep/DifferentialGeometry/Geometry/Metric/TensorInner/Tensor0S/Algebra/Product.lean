import dep.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.Expansion
import dep.DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric
import dep.DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Covariant

set_option autoImplicit false

namespace DifferentialGeometry
namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem inner0S_product_one_two
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (α β : Tensor0SSpace 1 I x)
    (A B : Tensor0SSpace 2 I x) :
    inner0S (I := I) g x 3
        (Tensor0SSpace.product (r := 1) (s := 2) α A)
        (Tensor0SSpace.product (r := 1) (s := 2) β B) =
      inner0S (I := I) g x 1 α β *
        inner0S (I := I) g x 2 A B  := by sorry

theorem inner0S_three_product_right
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (N : Tensor0SSpace 3 I x)
    (α : Tensor0SSpace 1 I x)
    (A : Tensor0SSpace 2 I x) :
    inner0S (I := I) g x 3 N
        (Tensor0SSpace.product (r := 1) (s := 2) α A) =
      inner0S (I := I) g x 2
        ((tensor0SCurry (I := I) (𝕜 := Real) (M := M) 2 x N)
          (cotangentSharp (I := I) g x α))
        A  := by sorry

theorem normSq0S_smul_sub_product_one_two
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (r : Real)
    (N : Tensor0SSpace 3 I x)
    (α : Tensor0SSpace 1 I x)
    (A : Tensor0SSpace 2 I x) :
    normSq0S (I := I) g x 3
        (r • N -
          Tensor0SSpace.product (r := 1) (s := 2) α A) =
      r ^ 2 * normSq0S (I := I) g x 3 N -
        2 * r * inner0S (I := I) g x 3 N
          (Tensor0SSpace.product (r := 1) (s := 2) α A) +
        inner0S (I := I) g x 1 α α *
          normSq0S (I := I) g x 2 A  := by sorry

theorem sum5_swap_first_last
    {Idx : Type*} [Fintype Idx]
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, F i j k l a) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, F a j k l i)  := by sorry

theorem sum5_swap_second_last
    {Idx : Type*} [Fintype Idx]
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, F i j k l a) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, F i a k l j)  := by sorry

theorem sum5_swap_third_last
    {Idx : Type*} [Fintype Idx]
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, F i j k l a) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, F i j a l k)  := by sorry

theorem sum5_swap_fourth_last
    {Idx : Type*} [Fintype Idx]
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, F i j k l a) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, F i j k a l)  := by sorry

theorem inner0S_two_metricCompatible_coord_correctionA1
    {Idx : Type*} [Fintype Idx]
    (U Γ A B : Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * ((∑ a : Idx, Γ i a * A a j) * B k l)) =
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      (∑ a : Idx, Γ a i * U a k) * U j l * A i j * B k l)  := by sorry

theorem inner0S_two_metricCompatible_coord_correctionA2
    {Idx : Type*} [Fintype Idx]
    (U Γ A B : Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * ((∑ a : Idx, Γ j a * A i a) * B k l)) =
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * (∑ a : Idx, Γ a j * U a l) * A i j * B k l)  := by sorry

theorem inner0S_two_metricCompatible_coord_correctionB1
    {Idx : Type*} [Fintype Idx]
    (U Γ A B : Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (A i j * (∑ a : Idx, Γ k a * B a l))) =
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      (∑ a : Idx, Γ a k * U i a) * U j l * A i j * B k l)  := by sorry

theorem inner0S_two_metricCompatible_coord_correctionB2
    {Idx : Type*} [Fintype Idx]
    (U Γ A B : Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (A i j * (∑ a : Idx, Γ l a * B k a))) =
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * (∑ a : Idx, Γ a l * U j a) * A i j * B k l)  := by sorry

private theorem sum_four_sub {Idx : Type*} [Fintype Idx]
    (f h : Idx → Idx → Idx → Idx → Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, (f i j k l - h i j k l)) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, f i j k l) -
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, h i j k l  := by sorry

private theorem sum_four_neg {Idx : Type*} [Fintype Idx]
    (f : Idx → Idx → Idx → Idx → Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, -f i j k l) =
      -(∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, f i j k l)  := by sorry

theorem inner0S_two_metricCompatible_coord_DU_first
    {Idx : Type*} [Fintype Idx]
    (U Γ A B DU : Idx -> Idx -> Real)
    (hDU : ∀ p q : Idx,
      DU p q =
        - ((∑ a : Idx, Γ a p * U a q) + (∑ a : Idx, Γ a q * U p a))) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      DU i k * U j l * A i j * B k l) =
      - (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * U j l * ((∑ a : Idx, Γ i a * A a j) * B k l)) -
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * U j l * (A i j * (∑ a : Idx, Γ k a * B a l)))  := by sorry

theorem inner0S_two_metricCompatible_coord_DU_second
    {Idx : Type*} [Fintype Idx]
    (U Γ A B DU : Idx -> Idx -> Real)
    (hDU : ∀ p q : Idx,
      DU p q =
        - ((∑ a : Idx, Γ a p * U a q) + (∑ a : Idx, Γ a q * U p a))) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * DU j l * A i j * B k l) =
      - (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * U j l * ((∑ a : Idx, Γ j a * A i a) * B k l)) -
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * U j l * (A i j * (∑ a : Idx, Γ l a * B k a)))  := by sorry

theorem inner0S_two_metricCompatible_coord_NA_sum
    {Idx : Type*} [Fintype Idx]
    (U Γ A B DA NA : Idx -> Idx -> Real)
    (hNA : ∀ p q : Idx,
      NA p q =
        DA p q - (∑ a : Idx, Γ p a * A a q) -
          (∑ a : Idx, Γ q a * A p a)) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (NA i j * B k l)) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (DA i j * B k l)) -
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * ((∑ a : Idx, Γ i a * A a j) * B k l)) -
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * ((∑ a : Idx, Γ j a * A i a) * B k l))  := by sorry

theorem inner0S_two_metricCompatible_coord_NB_sum
    {Idx : Type*} [Fintype Idx]
    (U Γ A B DB NB : Idx -> Idx -> Real)
    (hNB : ∀ p q : Idx,
      NB p q =
        DB p q - (∑ a : Idx, Γ p a * B a q) -
          (∑ a : Idx, Γ q a * B p a)) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (A i j * NB k l)) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (A i j * DB k l)) -
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (A i j * (∑ a : Idx, Γ k a * B a l))) -
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (A i j * (∑ a : Idx, Γ l a * B k a)))  := by sorry

theorem inner0S_two_metricCompatible_scalar_sum_algebra
    (P Q A1 A2 B1 B2 : Real) :
    (-A1 - B1) + (-A2 - B2) + P + Q =
      (P - A1 - A2) + (Q - B1 - B2)  := by sorry

theorem inner0S_two_metricCompatible_coord_algebra
    {Idx : Type*} [Fintype Idx]
    (U Γ A B DA DB NA NB DU : Idx -> Idx -> Real)
    (hDU : ∀ p q : Idx,
      DU p q =
        - ((∑ a : Idx, Γ a p * U a q) + (∑ a : Idx, Γ a q * U p a)))
    (hNA : ∀ p q : Idx,
      NA p q =
        DA p q - (∑ a : Idx, Γ p a * A a q) -
          (∑ a : Idx, Γ q a * A p a))
    (hNB : ∀ p q : Idx,
      NB p q =
        DB p q - (∑ a : Idx, Γ p a * B a q) -
          (∑ a : Idx, Γ q a * B p a)) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      ((DU i k * U j l + U i k * DU j l) * A i j * B k l +
        U i k * U j l * (DA i j * B k l + A i j * DB k l))) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (NA i j * B k l + A i j * NB k l))  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem deriv4sum
    {Idx : Type*} [Fintype Idx]
    (U A B : M -> Idx -> Idx -> Real)
    {x : M} (v : TangentSpace I x)
    (hU : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => U y i j) x)
    (hA : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => A y i j) x)
    (hB : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => B y i j) x) :
    mvfderiv (I := I)
        (fun y : M => ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U y i k * U y j l * A y i j * B y k l) x v =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        (((mvfderiv (I := I) (fun y : M => U y i k) x v) * U x j l +
            U x i k * (mvfderiv (I := I) (fun y : M => U y j l) x v)) *
            A x i j * B x k l +
          U x i k * U x j l *
            ((mvfderiv (I := I) (fun y : M => A y i j) x v) * B x k l +
              A x i j * (mvfderiv (I := I) (fun y : M => B y k l) x v)))  := by sorry

theorem fin2_apply_ite {α β : Type*} (f : α -> β) (i j : α) :
    (fun q : Fin 2 => f (if q = 0 then i else j)) =
      fun q : Fin 2 => if q = 0 then f i else f j  := by sorry

end

end Tensor0SBundle
end DifferentialGeometry

