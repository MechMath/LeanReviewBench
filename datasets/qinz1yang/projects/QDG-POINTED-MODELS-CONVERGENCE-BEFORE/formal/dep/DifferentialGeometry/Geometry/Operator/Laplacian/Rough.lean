import dep.DifferentialGeometry.Geometry.Curvature.Sections.Connection
import dep.DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Inverse
import dep.DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Covariant
import dep.DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Coordinate
import dep.DifferentialGeometry.Geometry.Metric.MetricFiberData.Hom
import dep.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.Expansion
import dep.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import dep.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Algebra.Product
import dep.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Calculus.CovariantDerivative
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Operator

noncomputable section

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def metricTraceInput {x : M} {s : ℕ}
    (X Y : TangentSpace I x) (tail : Fin s -> TangentSpace I x) :
    Fin (s + 2) -> TangentSpace I x :=
  Fin.cases X (Fin.cases Y tail)

def metricTensor0S (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  (((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm.toContinuousLinearMap).comp
    (g.inner x)).uncurryLeft

@[simp]
theorem metricTensor0S_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 -> TangentSpace I x) :
    metricTensor0S (I := I) g x v = g.inner x (v 0) (v 1)  := by sorry

def metricTracePair0SAt (g : SmoothRiemannianMetric I M)
    {x : M}
    (B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Real :=
  inner0S (I := I) g x 2 (metricTensor0S (I := I) g x) B

omit [FiniteDimensional ℝ E] in
private theorem tensor0S_curry_apply_cons_local
    {x : M} (s : ℕ)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (X : TangentSpace I x) (tail : Fin s -> TangentSpace I x) :
    (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x A X) tail =
      A (Fin.cons X tail)  := by sorry

omit [FiniteDimensional ℝ E] in
private theorem tensor0SSpace_sum_apply {ι : Type*} [Fintype ι] {x : M} {s : ℕ}
    (T : ι -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (v : Fin s -> TangentSpace I x) :
    ((∑ i : ι, T i) v) = ∑ i : ι, (T i) v  := by sorry

omit [FiniteDimensional ℝ E] in
private theorem tensor0SSpace_smul_apply {x : M} {s : ℕ}
    (c : Real)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (v : Fin s -> TangentSpace I x) :
    (c • T) v = c * T v  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem metricTraceInput_update_first {x : M} {s : ℕ}
    (v : Fin 2 -> TangentSpace I x) (tail : Fin s -> TangentSpace I x)
    (X : TangentSpace I x) :
    metricTraceInput (I := I) X (v 1) tail =
      Function.update (metricTraceInput (I := I) (v 0) (v 1) tail)
        (0 : Fin (s + 2)) X  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem metricTraceInput_update_second {x : M} {s : ℕ}
    (v : Fin 2 -> TangentSpace I x) (tail : Fin s -> TangentSpace I x)
    (Y : TangentSpace I x) :
    metricTraceInput (I := I) (v 0) Y tail =
      Function.update (metricTraceInput (I := I) (v 0) (v 1) tail)
        (1 : Fin (s + 2)) Y  := by sorry

omit [FiniteDimensional ℝ E] in
theorem exists_freezeFirstTwo0S {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    ∃ B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x,
      ∀ X Y : TangentSpace I x,
        B (vec2 (I := I) X Y) = T (metricTraceInput (I := I) X Y tail)  := by sorry

def freezeFirstTwo0S {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  Classical.choose (exists_freezeFirstTwo0S (I := I) T tail)

omit [FiniteDimensional ℝ E] in
@[simp]
theorem freezeFirstTwo0S_apply {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) (X Y : TangentSpace I x) :
    freezeFirstTwo0S (I := I) T tail (vec2 (I := I) X Y) =
      T (metricTraceInput (I := I) X Y tail)  := by sorry

def freezeFirstTwoArgs0S {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (X Y : TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x :=
  tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
    (tensor0SCurry (I := I) (𝕜 := Real) (M := M) (s + 1) x T X) Y

omit [FiniteDimensional ℝ E] in
@[simp]
theorem freezeFirstTwoArgs0S_apply {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (X Y : TangentSpace I x) (tail : Fin s -> TangentSpace I x) :
    freezeFirstTwoArgs0S (I := I) T X Y tail =
      T (metricTraceInput (I := I) X Y tail)  := by sorry

omit [FiniteDimensional ℝ E] in
theorem exists_freezeLastTwo0S3 {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y : TangentSpace I x) :
    ∃ B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x,
      ∀ X Z : TangentSpace I x,
        B (vec2 (I := I) X Z) = T (vec3 (I := I) Y X Z)  := by sorry

def freezeLastTwo0S3 {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y : TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  Classical.choose (exists_freezeLastTwo0S3 (I := I) T Y)

omit [FiniteDimensional ℝ E] in
@[simp]
theorem freezeLastTwo0S3_apply {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y X Z : TangentSpace I x) :
    freezeLastTwo0S3 (I := I) T Y (vec2 (I := I) X Z) =
      T (vec3 (I := I) Y X Z)  := by sorry

def metricTraceFirstTwo0SAt (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) : Real :=
  metricTracePair0SAt (I := I) g (freezeFirstTwo0S (I := I) T tail)

theorem freezeFirstTwo0S_neg {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    freezeFirstTwo0S (I := I) (-T) tail = -(freezeFirstTwo0S (I := I) T tail)  := by sorry

theorem freezeFirstTwo0S_add {x : M} {s : ℕ}
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    freezeFirstTwo0S (I := I) (A + B) tail =
      freezeFirstTwo0S (I := I) A tail + freezeFirstTwo0S (I := I) B tail  := by sorry

theorem freezeFirstTwo0S_smul {x : M} {s : ℕ} (c : Real)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    freezeFirstTwo0S (I := I) (c • T) tail = c • freezeFirstTwo0S (I := I) T tail  := by sorry

theorem metricTracePair0SAt_neg (g : SmoothRiemannianMetric I M) {x : M}
    (B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    metricTracePair0SAt (I := I) g (-B) = -metricTracePair0SAt (I := I) g B  := by sorry

theorem metricTracePair0SAt_add (g : SmoothRiemannianMetric I M) {x : M}
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    metricTracePair0SAt (I := I) g (A + B) =
      metricTracePair0SAt (I := I) g A + metricTracePair0SAt (I := I) g B  := by sorry

theorem metricTracePair0SAt_smul (g : SmoothRiemannianMetric I M) {x : M} (c : Real)
    (B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    metricTracePair0SAt (I := I) g (c • B) = c * metricTracePair0SAt (I := I) g B  := by sorry

theorem metricTracePair0SAt_sub (g : SmoothRiemannianMetric I M) {x : M}
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    metricTracePair0SAt (I := I) g (A - B) =
      metricTracePair0SAt (I := I) g A - metricTracePair0SAt (I := I) g B  := by sorry

theorem metricTraceFirstTwo0SAt_neg (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) g (-T) tail = -metricTraceFirstTwo0SAt (I := I) g T tail  := by sorry

theorem metricTraceFirstTwo0SAt_add (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) g (A + B) tail =
      metricTraceFirstTwo0SAt (I := I) g A tail +
        metricTraceFirstTwo0SAt (I := I) g B tail  := by sorry

theorem metricTraceFirstTwo0SAt_smul (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ} (c : Real)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) g (c • T) tail = c * metricTraceFirstTwo0SAt
      (I := I) g T tail  := by sorry

theorem metricTraceFirstTwo0SAt_sub (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) g (A - B) tail =
      metricTraceFirstTwo0SAt (I := I) g A tail -
        metricTraceFirstTwo0SAt (I := I) g B tail  := by sorry

def metricTraceLastTwo0SAt3 (g : SmoothRiemannianMetric I M)
    {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y : TangentSpace I x) : Real :=
  metricTracePair0SAt (I := I) g (freezeLastTwo0S3 (I := I) T Y)

def metricTrace0S2InBasis
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) : Real :=
  ∑ i : Idx, ∑ j : Idx,
    gInv i j * T (metricTraceInput (I := I) (basis i) (basis j) tail)

def metricTrace0S2TensorInBasis
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x :=
  ∑ i : Idx, ∑ j : Idx,
    gInv i j • freezeFirstTwoArgs0S (I := I) T (basis i) (basis j)

omit [FiniteDimensional ℝ E] in
@[simp]
theorem metricTrace0S2TensorInBasis_apply
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTrace0S2TensorInBasis (I := I) basis gInv T tail =
      metricTrace0S2InBasis (I := I) basis gInv T tail  := by sorry

omit [FiniteDimensional ℝ E] in
private theorem metricInverseInBasis_contract_left
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (j k : Idx) :
    (∑ i : Idx, gInv i k * g.inner x (basis i) (basis j)) =
      (if j = k then 1 else 0)  := by sorry

omit [FiniteDimensional ℝ E] in
private theorem metricInverseInBasis_contract_metric
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (k l : Idx) :
    (∑ i : Idx, ∑ j : Idx,
      gInv i k * gInv j l * g.inner x (basis i) (basis j)) =
        gInv k l  := by sorry

theorem metricTracePair0SAt_eq_sum_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    metricTracePair0SAt (I := I) g B =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * B (vec2 (I := I) (basis i) (basis j))  := by sorry

theorem normSq0S_metricTensor0S_eq_card
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv) :
    normSq0S (I := I) g x 2 (metricTensor0S (I := I) g x) =
      (Fintype.card Idx : Real)  := by sorry

theorem metricTracePair0SAt_metric
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricTracePair0SAt (I := I) g (metricTensor0S (I := I) g x) =
      (Module.finrank Real E : Real)  := by sorry

theorem metricTracePair0SAt_sq_le_card_mul_normSq0S
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    (metricTracePair0SAt (I := I) g A) ^ 2 <=
      (Fintype.card Idx : Real) * normSq0S (I := I) g x 2 A  := by sorry

theorem trace_sub_le_c0
    (g h : SmoothRiemannianMetric I M) (x : M)
    {C : Real} (hC : 1 ≤ C)
    (hequiv : ∀ v : TangentSpace I x,
      C⁻¹ * g.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ C * g.inner x v v)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 x) :
    |metricTracePair0SAt (I := I) h A -
        metricTracePair0SAt (I := I) g A| ≤
      (Module.finrank Real (TangentSpace I x) : Real) * C *
        Real.sqrt
          (normSq0S (I := I) g x 2
            (metricTensor0S (I := I) h x -
              metricTensor0S (I := I) g x)) *
        Real.sqrt (normSq0S (I := I) g x 2 A)  := by sorry

theorem metricTracePair0SAt_sq_div_rank_le_normSq0S
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] [Nonempty Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    (1 / (Fintype.card Idx : Real)) *
        (metricTracePair0SAt (I := I) g A) ^ 2 <=
      normSq0S (I := I) g x 2 A  := by sorry

theorem metricTraceFirstTwo0SAt_eq_sum_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) g T tail =
      metricTrace0S2InBasis (I := I) basis gInv T tail  := by sorry

theorem metricTraceLastTwo0SAt3_eq_sum_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y : TangentSpace I x) :
    metricTraceLastTwo0SAt3 (I := I) g T Y =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * T (vec3 (I := I) Y (basis i) (basis j))  := by sorry

theorem metricTrace0S2InBasis_eq_metricTrace
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTrace0S2InBasis (I := I) basis gInv T tail =
      metricTraceFirstTwo0SAt (I := I) g T tail  := by sorry

theorem metricTrace0S2InBasis_eq_metricTrace0S2InBasis
    (g : SmoothRiemannianMetric I M)
    {Idx₁ Idx₂ : Type*} [Fintype Idx₁] [DecidableEq Idx₁]
    [Fintype Idx₂] [DecidableEq Idx₂]
    {x : M}
    (basis₁ : Module.Basis Idx₁ Real (TangentSpace I x))
    (gInv₁ : Idx₁ -> Idx₁ -> Real)
    (hinv₁ : MetricInverseInBasis (I := I) g x basis₁ gInv₁)
    (basis₂ : Module.Basis Idx₂ Real (TangentSpace I x))
    (gInv₂ : Idx₂ -> Idx₂ -> Real)
    (hinv₂ : MetricInverseInBasis (I := I) g x basis₂ gInv₂)
    {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTrace0S2InBasis (I := I) basis₁ gInv₁ T tail =
      metricTrace0S2InBasis (I := I) basis₂ gInv₂ T tail  := by sorry

def metricTraceFirstTwo0STensor
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x :=
  metricTrace0S2TensorInBasis (I := I)
    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x)
    (fun k l : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChartComponent (I := I) g x k
        l
        (extChartAt I x x))
    T

@[simp]
theorem metricTraceFirstTwo0STensor_apply
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTraceFirstTwo0STensor (I := I) g T tail =
      metricTraceFirstTwo0SAt (I := I) g T tail  := by sorry

def roughLap0STensor
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x :=
  metricTraceFirstTwo0STensor (I := I) g nabla2A

@[simp]
theorem roughLap0STensor_apply
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    roughLap0STensor (I := I) g nabla2A tail =
      metricTraceFirstTwo0SAt (I := I) g nabla2A tail  := by sorry

theorem trace_smul_leibniz
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    {s : ℕ}
    (f : Real)
    (df : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (hessF : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (nabla2A nabla2fA :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s + 2) x)
    (tail : Fin s -> TangentSpace I x)
    (hleib :
      ∀ X Y : TangentSpace I x, ∀ tail : Fin s -> TangentSpace I x,
        nabla2fA (metricTraceInput (I := I) X Y tail) =
          hessF (metricTraceInput (I := I) X Y Fin.elim0) * A tail +
            df (fun _ : Fin 1 => X) * nablaA (Fin.cons Y tail) +
            df (fun _ : Fin 1 => Y) * nablaA (Fin.cons X tail) +
            f * nabla2A (metricTraceInput (I := I) X Y tail)) :
    metricTraceFirstTwo0SAt (I := I) g nabla2fA tail =
      metricTraceFirstTwo0SAt (I := I) g hessF Fin.elim0 * A tail +
        (∑ i : Idx, ∑ j : Idx,
          gInv i j *
            (df (fun _ : Fin 1 => basis i) *
                nablaA (Fin.cons (basis j) tail) +
              df (fun _ : Fin 1 => basis j) *
                nablaA (Fin.cons (basis i) tail))) +
        f * metricTraceFirstTwo0SAt (I := I) g nabla2A tail  := by sorry

theorem trace_smul_parallel
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    {s : ℕ}
    (f : Real)
    (df : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (hessF : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (nabla2A nabla2fA :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s + 2) x)
    (tail : Fin s -> TangentSpace I x)
    (hfirst : ∀ X : TangentSpace I x, ∀ tail : Fin s -> TangentSpace I x,
      nablaA (Fin.cons X tail) = 0)
    (hsecond : ∀ X Y : TangentSpace I x, ∀ tail : Fin s -> TangentSpace I x,
      nabla2A (metricTraceInput (I := I) X Y tail) = 0)
    (hleib :
      ∀ X Y : TangentSpace I x, ∀ tail : Fin s -> TangentSpace I x,
        nabla2fA (metricTraceInput (I := I) X Y tail) =
          hessF (metricTraceInput (I := I) X Y Fin.elim0) * A tail +
            df (fun _ : Fin 1 => X) * nablaA (Fin.cons Y tail) +
            df (fun _ : Fin 1 => Y) * nablaA (Fin.cons X tail) +
            f * nabla2A (metricTraceInput (I := I) X Y tail)) :
    metricTraceFirstTwo0SAt (I := I) g nabla2fA tail =
      metricTraceFirstTwo0SAt (I := I) g hessF Fin.elim0 * A tail  := by sorry

theorem roughLap_smul_leib
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    {s : ℕ}
    (f : Real)
    (df : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (hessF : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (nabla2A nabla2fA :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s + 2) x)
    (tail : Fin s -> TangentSpace I x)
    (hleib :
      ∀ X Y : TangentSpace I x, ∀ tail : Fin s -> TangentSpace I x,
        nabla2fA (metricTraceInput (I := I) X Y tail) =
          hessF (metricTraceInput (I := I) X Y Fin.elim0) * A tail +
            df (fun _ : Fin 1 => X) * nablaA (Fin.cons Y tail) +
            df (fun _ : Fin 1 => Y) * nablaA (Fin.cons X tail) +
            f * nabla2A (metricTraceInput (I := I) X Y tail)) :
    roughLap0STensor (I := I) g nabla2fA tail =
      metricTraceFirstTwo0SAt (I := I) g hessF Fin.elim0 * A tail +
        (∑ i : Idx, ∑ j : Idx,
          gInv i j *
            (df (fun _ : Fin 1 => basis i) *
                nablaA (Fin.cons (basis j) tail) +
              df (fun _ : Fin 1 => basis j) *
                nablaA (Fin.cons (basis i) tail))) +
        f * roughLap0STensor (I := I) g nabla2A tail  := by sorry

theorem roughLap_smul_par
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    {s : ℕ}
    (f : Real)
    (df : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (hessF : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (nabla2A nabla2fA :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s + 2) x)
    (tail : Fin s -> TangentSpace I x)
    (hfirst : ∀ X : TangentSpace I x, ∀ tail : Fin s -> TangentSpace I x,
      nablaA (Fin.cons X tail) = 0)
    (hsecond : ∀ X Y : TangentSpace I x, ∀ tail : Fin s -> TangentSpace I x,
      nabla2A (metricTraceInput (I := I) X Y tail) = 0)
    (hleib :
      ∀ X Y : TangentSpace I x, ∀ tail : Fin s -> TangentSpace I x,
        nabla2fA (metricTraceInput (I := I) X Y tail) =
          hessF (metricTraceInput (I := I) X Y Fin.elim0) * A tail +
            df (fun _ : Fin 1 => X) * nablaA (Fin.cons Y tail) +
            df (fun _ : Fin 1 => Y) * nablaA (Fin.cons X tail) +
            f * nabla2A (metricTraceInput (I := I) X Y tail)) :
    roughLap0STensor (I := I) g nabla2fA tail =
      metricTraceFirstTwo0SAt (I := I) g hessF Fin.elim0 * A tail  := by sorry

def roughLap0SAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) : Real :=
  metricTrace0S2InBasis (I := I) basis gInv nabla2A tail

def roughLap1FormAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (Y : TangentSpace I x) : Real :=
  roughLap0SAt (I := I) basis gInv (s := 1) nabla2α (fun _ : Fin 1 => Y)

def RoughLap0SRealizesMetricTraceInBasis
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) : Prop :=
  ∀ tail : Fin s -> TangentSpace I x,
    roughA tail = roughLap0SAt (I := I) basis gInv nabla2A tail

omit [FiniteDimensional ℝ E] in
theorem roughLap0SAt_eq_of_realizes
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (h : RoughLap0SRealizesMetricTraceInBasis (I := I) basis gInv roughA nabla2A)
    (tail : Fin s -> TangentSpace I x) :
    roughA tail = roughLap0SAt (I := I) basis gInv nabla2A tail  := by sorry

omit [FiniteDimensional ℝ E] in
theorem roughLap1FormAt_eq_of_realizes
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (roughα : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : RoughLap0SRealizesMetricTraceInBasis (I := I) basis gInv (s := 1) roughα nabla2α)
    (Y : TangentSpace I x) :
    roughα (fun _ : Fin 1 => Y) =
      roughLap1FormAt (I := I) basis gInv nabla2α Y  := by sorry

def metricTrace0s
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (traceT : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x) : Prop :=
  ∀ tail : Fin s -> TangentSpace I x,
    traceT tail = metricTraceFirstTwo0SAt (I := I) g T tail

def RoughLap0SRealizesMetricTrace
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x)
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) : Prop :=
  metricTrace0s (I := I) g nabla2A roughA

def roughLap0s
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x) : Prop :=
  RoughLap0SRealizesMetricTrace (I := I) g roughA nabla2A

theorem metric_trace_0s_iff_eq_tensor
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (traceT : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x) :
    metricTrace0s (I := I) g T traceT ↔
      traceT = metricTraceFirstTwo0STensor (I := I) g T  := by sorry

theorem rough_lap_0s_iff_eq_tensor
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x) :
    roughLap0s (I := I) g nabla2A roughA ↔
      roughA = roughLap0STensor (I := I) g nabla2A  := by sorry

theorem roughLap0STensor_realizes
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) :
    roughLap0s (I := I) g nabla2A
      (roughLap0STensor (I := I) g nabla2A)  := by sorry

def roughLapOneForm
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (roughα : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 x) : Prop :=
  roughLap0s (I := I) g (s := 1) nabla2α roughα

theorem metric_trace_0s_apply_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} {s : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (traceT : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x)
    (htrace : metricTrace0s (I := I) g T traceT)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (tail : Fin s -> TangentSpace I x) :
    traceT tail = metricTrace0S2InBasis (I := I) basis gInv T tail  := by sorry

theorem rough_lap_0s_apply_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} {s : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x)
    (hrough : roughLap0s (I := I) g nabla2A roughA)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (tail : Fin s -> TangentSpace I x) :
    roughA tail = roughLap0SAt (I := I) basis gInv nabla2A tail  := by sorry

theorem rough_lap_one_form_apply_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (roughα : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 x)
    (hrough : roughLapOneForm (I := I) g nabla2α roughα)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Y : TangentSpace I x) :
    roughα (fun _ : Fin 1 => Y) =
      roughLap1FormAt (I := I) basis gInv nabla2α Y  := by sorry

theorem rough_lap_one_form_realizes_metric_trace
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (roughα : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 x)
    (hrough : roughLapOneForm (I := I) g nabla2α roughα)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv) :
    RoughLap0SRealizesMetricTraceInBasis (I := I) basis gInv
      (s := 1) roughα nabla2α  := by sorry

end

end DifferentialGeometry.Geometry.Operator

