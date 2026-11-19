import Mathlib.Analysis.InnerProductSpace.Spectrum
import dep.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.Expansion
import dep.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.KroneckerQuadraticForm
import dep.DifferentialGeometry.Tensor.RSTensor.Coordinates.CoordinateBasis

set_option autoImplicit false

namespace DifferentialGeometry
namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section DiagonalCoordinate

variable {Idx : Type*} [DecidableEq Idx]
variable {x : M}

def diagonalInvMetric (μ : Idx -> Real) : Idx -> Idx -> Real :=
  fun i j => if i = j then μ i else 0

def identityInvMetric : Idx -> Idx -> Real :=
  diagonalInvMetric (fun _ : Idx => 1)

@[simp] theorem diagonalInvMetric_apply_self (μ : Idx -> Real) (i : Idx) :
    diagonalInvMetric μ i i = μ i  := by sorry

@[simp] theorem identityInvMetric_apply_self (i : Idx) :
    identityInvMetric (Idx := Idx) i i = 1  := by sorry

theorem diagonalInvMetric_eq_zero_of_ne {μ : Idx -> Real} {i j : Idx}
    (hij : i ≠ j) :
    diagonalInvMetric μ i j = 0  := by sorry

private theorem prod_diagonalInvMetric_eq_zero_of_ne
    {s : Nat} {μ : Idx -> Real} {I0 J0 : Fin s -> Idx}
    (hIJ : I0 ≠ J0) :
    (∏ a : Fin s, diagonalInvMetric μ (I0 a) (J0 a)) = 0  := by sorry

omit [DecidableEq Idx] in
private theorem prod_mu_le_pow
    {s : Nat} {μ : Idx -> Real} {C : Real}
    (hμ_nonneg : forall i : Idx, 0 <= μ i)
    (hμ_le : forall i : Idx, μ i <= C)
    (I0 : Fin s -> Idx) :
    (∏ a : Fin s, μ (I0 a)) <= C ^ s  := by sorry

variable [Fintype Idx]

omit [FiniteDimensional ℝ E] in
theorem metricInverseInBasis_identity_of_orthonormal
    (g : SmoothRiemannianMetric I M) (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0) :
    MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx))  := by sorry

omit [FiniteDimensional ℝ E] in
theorem coordInner0S_diagonal_eq_sum
    (s : Nat) (μ : Idx -> Real)
    (A : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) s (diagonalInvMetric μ) A A basis =
      ∑ I0 : Fin s -> Idx,
        (∏ a : Fin s, μ (I0 a)) *
          (tensor0SComponent (I := I) A (fun i => basis i) I0) ^ 2  := by sorry

omit [FiniteDimensional ℝ E] in
theorem coordInner0S_identity_eq_sum_sq
    (s : Nat) (A : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) s identityInvMetric A A basis =
      ∑ I0 : Fin s -> Idx,
        (tensor0SComponent (I := I) A (fun i => basis i) I0) ^ 2  := by sorry

omit [FiniteDimensional ℝ E] in
theorem coordInner0S_identity_eq_sum
    (s : Nat) (A B : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) s identityInvMetric A B basis =
      ∑ I0 : Fin s -> Idx,
        tensor0SComponent (I := I) A (fun i => basis i) I0 *
          tensor0SComponent (I := I) B (fun i => basis i) I0  := by sorry

theorem inner0S_basisTensor_left_identity
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (slots : Fin s -> Idx) (A : Tensor0SSpace s I x) :
    inner0S (I := I) g x s (basisTensor0S (I := I) basis slots) A =
      component0S (I := I) basis A slots  := by sorry

theorem inner0S_basisTensor_right_identity
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    inner0S (I := I) g x s A (basisTensor0S (I := I) basis slots) =
      component0S (I := I) basis A slots  := by sorry

theorem normSq0S_identity_eq_sum_sq
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s A =
      ∑ slots : Fin s -> Idx,
        (component0S (I := I) basis A slots) ^ 2  := by sorry

theorem normSq0S_curry_sum
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : Tensor0SSpace (s + 1) I x) :
    (∑ i : Idx,
        normSq0S (I := I) g x s
          (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x A (basis i))) =
      normSq0S (I := I) g x (s + 1) A  := by sorry

theorem normSq0S_le_card_of_component_bound
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : Tensor0SSpace s I x) (B : Real) (hBnn : 0 ≤ B)
    (hB : ∀ slots : Fin s -> Idx,
      |component0S (I := I) basis A slots| ≤ B) :
    normSq0S (I := I) g x s A ≤
      (Fintype.card (Fin s -> Idx) : Real) * B ^ 2  := by sorry

theorem sqrt_normSq0S_le_card_of_component_bound
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : Tensor0SSpace s I x) (B : Real) (hBnn : 0 ≤ B)
    (hB : ∀ slots : Fin s -> Idx,
      |component0S (I := I) basis A slots| ≤ B) :
    Real.sqrt (normSq0S (I := I) g x s A) ≤
      Real.sqrt (Fintype.card (Fin s -> Idx) : Real) * B  := by sorry

theorem normSq0S_three_identity_eq_sum
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : Tensor0SSpace 3 I x) :
    normSq0S (I := I) g x 3 A =
      ∑ d : Idx, ∑ a : Idx, ∑ b : Idx,
        (component0S (I := I) basis A
          (Fin.cons d (fun q : Fin 2 => if q = 0 then a else b))) ^ 2  := by sorry

omit [FiniteDimensional ℝ E] in
theorem coordInner0S_diagonal_le_pow_identity
    (s : Nat) (μ : Idx -> Real) (C : Real)
    (hμ_nonneg : forall i : Idx, 0 <= μ i)
    (hμ_le : forall i : Idx, μ i <= C)
    (A : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) s (diagonalInvMetric μ) A A basis <=
      C ^ s * coordInner0S (I := I) (x := x) s identityInvMetric A A basis  := by sorry

omit [FiniteDimensional ℝ E] in
theorem coordInner0S_identity_le_pow_diagonal
    (s : Nat) (μ : Idx -> Real) (m : Real) (hm : 0 < m)
    (hμ_lb : forall i : Idx, m <= μ i)
    (A : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) s identityInvMetric A A basis <=
      (1 / m) ^ s *
        coordInner0S (I := I) (x := x) s (diagonalInvMetric μ) A A basis  := by sorry

theorem normSq0S_diag_le
    (g h : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (μ : Idx -> Real) (C : Real)
    (hginv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (hhinv :
      MetricInverseInBasis (I := I) h x basis (diagonalInvMetric μ))
    (hμ_nonneg : forall i : Idx, 0 <= μ i)
    (hμ_le : forall i : Idx, μ i <= C)
    (A : Tensor0SSpace s I x) :
    normSq0S (I := I) h x s A <= C ^ s * normSq0S (I := I) g x s A  := by sorry

omit [FiniteDimensional ℝ E] in
theorem coordInner0S_identity_le_pow_quad
    (s : Nat) (Q : Idx -> Idx -> Real) (C : Real) (hC : 0 < C)
    (hQsymm : forall i j : Idx, Q i j = Q j i)
    (hQlb : forall w : Idx -> Real,
      (1 / C) * ∑ i : Idx, w i ^ 2 <= ∑ i : Idx, ∑ j : Idx, Q i j * (w i * w j))
    (A : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) s identityInvMetric A A basis <=
      C ^ s * coordInner0S (I := I) (x := x) s Q A A basis  := by sorry

theorem sum_comp_sq_le_pow_normSq0S
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Q : Idx -> Idx -> Real) (C : Real) (hC : 0 < C)
    (hginv : MetricInverseInBasis (I := I) g x basis Q)
    (hQsymm : forall i j : Idx, Q i j = Q j i)
    (hQlb : forall w : Idx -> Real,
      (1 / C) * ∑ i : Idx, w i ^ 2 <= ∑ i : Idx, ∑ j : Idx, Q i j * (w i * w j))
    (A : Tensor0SSpace s I x) :
    (∑ I0 : Fin s -> Idx,
        tensor0SComponent (I := I) A (fun i => basis i) I0 ^ 2) <=
      C ^ s * normSq0S (I := I) g x s A  := by sorry

theorem normSq0S_le_pow_sum_comp_sq
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Q : Idx -> Idx -> Real) (ε : Real) (hε0 : 0 <= ε)
    (hginv : MetricInverseInBasis (I := I) g x basis Q)
    (hnear : forall i j : Idx, |Q i j - (if i = j then (1 : Real) else 0)| <= ε)
    (A : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s A <=
      ((1 + ε) * (Fintype.card Idx : Real)) ^ s *
        ∑ I0 : Fin s -> Idx,
          tensor0SComponent (I := I) A (fun i => basis i) I0 ^ 2  := by sorry

end DiagonalCoordinate

section MetricEquiv

theorem exists_diagInv_of_equiv
    (g h : SmoothRiemannianMetric I M) (x : M) {C : Real}
    (hC : 1 <= C)
    (hequiv :
      forall v : TangentSpace I x,
        C⁻¹ * g.inner x v v <= h.inner x v v /\
          h.inner x v v <= C * g.inner x v v) :
    exists mu : Fin (Module.finrank Real (TangentSpace I x)) -> Real,
    exists basis :
      Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
        (TangentSpace I x),
      MetricInverseInBasis
        (I := I) g x basis
        (identityInvMetric
          (Idx := Fin (Module.finrank Real (TangentSpace I x)))) /\
      MetricInverseInBasis
        (I := I) h x basis (diagonalInvMetric mu) /\
      (forall i : Fin (Module.finrank Real (TangentSpace I x)), 0 <= mu i) /\
      (forall i : Fin (Module.finrank Real (TangentSpace I x)), mu i <= C)  := by sorry

omit [FiniteDimensional ℝ E] in
theorem metric_equiv_symm
    (g h : SmoothRiemannianMetric I M) (x : M) {C : Real}
    (hC : 1 <= C)
    (hequiv :
      forall v : TangentSpace I x,
        C⁻¹ * g.inner x v v <= h.inner x v v /\
          h.inner x v v <= C * g.inner x v v) :
    forall v : TangentSpace I x,
      C⁻¹ * h.inner x v v <= g.inner x v v /\
        g.inner x v v <= C * h.inner x v v  := by sorry

theorem normSq0S_upper_le_of_equiv
    (g h : SmoothRiemannianMetric I M) (x : M) (s : Nat) {C : Real}
    (hC : 1 <= C)
    (hequiv :
      forall v : TangentSpace I x,
        C⁻¹ * g.inner x v v <= h.inner x v v /\
          h.inner x v v <= C * g.inner x v v)
    (T : Tensor0SSpace s I x) :
    normSq0S (I := I) h x s T <=
      C ^ s * normSq0S (I := I) g x s T  := by sorry

theorem normSq0S_lower_le_of_equiv
    (g h : SmoothRiemannianMetric I M) (x : M) (s : Nat) {C : Real}
    (hC : 1 <= C)
    (hequiv :
      forall v : TangentSpace I x,
        C⁻¹ * g.inner x v v <= h.inner x v v /\
          h.inner x v v <= C * g.inner x v v)
    (T : Tensor0SSpace s I x) :
    (C ^ s)⁻¹ * normSq0S (I := I) g x s T <=
      normSq0S (I := I) h x s T  := by sorry

theorem normSq0S_le_of_metric_equiv
    (g h : SmoothRiemannianMetric I M) (x : M) (s : Nat) {C : Real}
    (hC : 1 <= C)
    (hequiv :
      forall v : TangentSpace I x,
        C⁻¹ * g.inner x v v <= h.inner x v v /\
          h.inner x v v <= C * g.inner x v v)
    (T : Tensor0SSpace s I x) :
    C ^ (-(s : Int)) * normSq0S (I := I) g x s T <=
      normSq0S (I := I) h x s T /\
    normSq0S (I := I) h x s T <=
      C ^ (s : Int) * normSq0S (I := I) g x s T  := by sorry

theorem sqrt_normSq0S_le_of_metric_equiv
    (g h : SmoothRiemannianMetric I M) (x : M) (s : Nat) {C : Real}
    (hC : 1 <= C)
    (hequiv :
      forall v : TangentSpace I x,
        C⁻¹ * g.inner x v v <= h.inner x v v /\
          h.inner x v v <= C * g.inner x v v)
    (T : Tensor0SSpace s I x) :
    Real.sqrt (normSq0S (I := I) h x s T) <=
      Real.sqrt (C ^ s) * Real.sqrt (normSq0S (I := I) g x s T)  := by sorry

end MetricEquiv

section PointwiseCS

theorem exists_orthonormal_basis
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ basis :
        Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
          (TangentSpace I x),
      ∀ i j,
        g.inner x (basis i) (basis j) =
          if i = j then (1 : Real) else 0  := by sorry

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

omit [FiniteDimensional ℝ E] in
theorem metricInverseInBasis_of_orthonormal
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (basis i) (basis j) = if i = j then 1 else 0) :
    MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Idx))  := by sorry

private theorem sqrt_prod {α : Type*} (s : Finset α) (f : α -> Real)
    (hf : ∀ a ∈ s, 0 <= f a) :
    Real.sqrt (∏ a ∈ s, f a) = ∏ a ∈ s, Real.sqrt (f a)  := by sorry

omit [Fintype Idx] in
theorem abs_apply_le_sqrt_normSq0S [Finite Idx]
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : forall i j : Idx,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (T : Tensor0SSpace s I x) (v : Fin s -> TangentSpace I x) :
    |T v| <=
      Real.sqrt (normSq0S (I := I) g x s T) *
        ∏ a : Fin s, Real.sqrt (g.inner x (v a) (v a))  := by sorry

theorem abs_apply_le_norm0S
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (T : Tensor0SSpace s I x) (v : Fin s -> TangentSpace I x) :
    |T v| <=
      Real.sqrt (normSq0S (I := I) g x s T) *
        ∏ a : Fin s, Real.sqrt (g.inner x (v a) (v a))  := by sorry

end PointwiseCS

end

end Tensor0SBundle
end DifferentialGeometry

