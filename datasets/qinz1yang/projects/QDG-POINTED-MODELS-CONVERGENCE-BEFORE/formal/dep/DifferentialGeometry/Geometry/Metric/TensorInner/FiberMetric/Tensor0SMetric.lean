import dep.DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian
import dep.DifferentialGeometry.Geometry.Metric.MetricFiberData.Hom
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Trace
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars

namespace DifferentialGeometry
namespace Tensor0SBundle

noncomputable section


open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]



def scalarMetricData (x : M) :
  MetricFiberData (Tensor0SSpace 0 I x) :=
  MetricFiberData.pullback
    ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) (M := M) 0 x).toLinearEquiv.trans
      (continuousMultilinearCurryFin0 Real (TangentSpace I x) Real).toLinearEquiv)
    MetricFiberData.real

def tensor0SMetricStep
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (D : MetricFiberData (Tensor0SSpace s I x)) :
    MetricFiberData (Tensor0SSpace (s + 1) I x) :=
  have hTopAdd0 : IsTopologicalAddGroup (Tensor0SSpace s I x) :=
    Bundle.continuousMultilinearMap.instIsTopologicalAddGroup
      (𝕜 := Real) (F := E) (E := TangentSpace I) s x
  letI : IsTopologicalAddGroup (Tensor0SSpace s I x) := hTopAdd0
  have hContAdd0 : ContinuousAdd (Tensor0SSpace s I x) :=
    IsTopologicalAddGroup.toContinuousAdd
  letI : ContinuousAdd (Tensor0SSpace s I x) := hContAdd0
  have hContSMul0 : ContinuousSMul Real (Tensor0SSpace s I x) :=
    Bundle.continuousMultilinearMap.instContinuousSMul
      (𝕜 := Real) (F := E) (E := TangentSpace I) s x
  letI : ContinuousSMul Real (Tensor0SSpace s I x) := hContSMul0
  letI : ContinuousConstSMul Real (Tensor0SSpace s I x) := inferInstance
  letI : TopologicalSpace (TangentSpace I x →L[Real] Tensor0SSpace s I x) :=
    @ContinuousLinearMap.topologicalSpace
      Real Real inferInstance inferInstance (RingHom.id Real)
      (TangentSpace I x) (Tensor0SSpace s I x)
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance hTopAdd0
  letI : AddCommGroup (TangentSpace I x →L[Real] Tensor0SSpace s I x) :=
    @ContinuousLinearMap.addCommGroup
      Real inferInstance Real inferInstance
      (TangentSpace I x) inferInstance inferInstance
      (Tensor0SSpace s I x) inferInstance inferInstance
      inferInstance inferInstance (RingHom.id Real) hTopAdd0
  letI : Module Real (TangentSpace I x →L[Real] Tensor0SSpace s I x) :=
    @ContinuousLinearMap.module
      Real Real Real inferInstance inferInstance inferInstance
      (TangentSpace I x) inferInstance inferInstance inferInstance
      (Tensor0SSpace s I x) inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      (RingHom.id Real) hContAdd0
  letI : FiniteDimensional Real (TangentSpace I x →L[Real] Tensor0SSpace s I x) :=
    (@LinearMap.toContinuousLinearMap
      Real inferInstance
      (TangentSpace I x) inferInstance inferInstance inferInstance inferInstance inferInstance
      (Tensor0SSpace s I x) inferInstance inferInstance inferInstance hTopAdd0 hContSMul0
      inferInstance inferInstance inferInstance).finiteDimensional
  MetricFiberData.pullback
    (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x).toLinearEquiv
    (@MetricFiberData.homCLM
      (TangentSpace I x) (Tensor0SSpace s I x)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance
      inferInstance inferInstance inferInstance hTopAdd0 hContSMul0 inferInstance
      (tangentMetricData (I := I) g x).metric D)

def tensor0SMetricData (g : SmoothRiemannianMetric I M) (x : M) :
    (s : Nat) -> MetricFiberData (Tensor0SSpace s I x)
  | 0 => scalarMetricData (I := I) x
  | 1 => cotangentMetricData (I := I) g x
  | s + 2 =>
      tensor0SMetricStep (I := I) g x (s + 1) (tensor0SMetricData g x (s + 1))

def inner0S
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) : Real :=
  (tensor0SMetricData (I := I) g x s).inner A B

theorem inner0S_symm {s : Nat}
    (g : SmoothRiemannianMetric I M) (x : M)
    (A B : Tensor0SSpace s I x) :
    inner0S (I := I) g x s A B = inner0S (I := I) g x s B A  := by sorry

theorem inner0S_add_left
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B C : Tensor0SSpace s I x) :
    inner0S (I := I) g x s (A + B) C =
      inner0S (I := I) g x s A C + inner0S (I := I) g x s B C  := by sorry

theorem inner0S_add_right
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B C : Tensor0SSpace s I x) :
    inner0S (I := I) g x s A (B + C) =
      inner0S (I := I) g x s A B + inner0S (I := I) g x s A C  := by sorry

theorem inner0S_sub_left
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B C : Tensor0SSpace s I x) :
    inner0S (I := I) g x s (A - B) C =
      inner0S (I := I) g x s A C - inner0S (I := I) g x s B C  := by sorry

def flat0S
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat) :
    Tensor0SSpace s I x ≃ₗ[Real] Module.Dual Real (Tensor0SSpace s I x) :=
  (tensor0SMetricData (I := I) g x s).flat

def normSq0S
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A : Tensor0SSpace s I x) : Real :=
  inner0S (I := I) g x s A A

noncomputable def tensor0SFiberNorm
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A : Tensor0SSpace s I x) : Real :=
  Real.sqrt (normSq0S (I := I) g x s A)

noncomputable def tensor04FiberNorm
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor0SSpace 4 I x) : Real :=
  tensor0SFiberNorm (I := I) g x 4 A

theorem tensor0S_inner_eq_inner0S
    (g : SmoothRiemannianMetric I M) (x : M) {s : Nat}
    (A B : Tensor0SSpace s I x) :
    letI : InnerProductSpace.Core Real (Tensor0SSpace s I x) :=
      (tensor0SMetricData (I := I) g x s).toCore
    letI : NormedAddCommGroup (Tensor0SSpace s I x) :=
      InnerProductSpace.Core.toNormedAddCommGroup
    letI : InnerProductSpace Real (Tensor0SSpace s I x) :=
      @InnerProductSpace.ofCore Real (Tensor0SSpace s I x) _ _ _
        (tensor0SMetricData (I := I) g x s).toCore.toCore
    inner Real A B = inner0S (I := I) g x s A B  := by sorry

theorem tensor0S_norm_sq_eq_normSq0S
    (g : SmoothRiemannianMetric I M) (x : M) {s : Nat}
    (A : Tensor0SSpace s I x) :
    letI : InnerProductSpace.Core Real (Tensor0SSpace s I x) :=
      (tensor0SMetricData (I := I) g x s).toCore
    letI : NormedAddCommGroup (Tensor0SSpace s I x) :=
      InnerProductSpace.Core.toNormedAddCommGroup
    letI : InnerProductSpace Real (Tensor0SSpace s I x) :=
      @InnerProductSpace.ofCore Real (Tensor0SSpace s I x) _ _ _
        (tensor0SMetricData (I := I) g x s).toCore.toCore
    ‖A‖ ^ 2 = normSq0S (I := I) g x s A  := by sorry

theorem tensor0SFiberNorm_eq_norm
    (g : SmoothRiemannianMetric I M) (x : M) {s : Nat}
    (A : Tensor0SSpace s I x) :
    letI : InnerProductSpace.Core Real (Tensor0SSpace s I x) :=
      (tensor0SMetricData (I := I) g x s).toCore
    letI : NormedAddCommGroup (Tensor0SSpace s I x) :=
      InnerProductSpace.Core.toNormedAddCommGroup
    letI : InnerProductSpace Real (Tensor0SSpace s I x) :=
      @InnerProductSpace.ofCore Real (Tensor0SSpace s I x) _ _ _
        (tensor0SMetricData (I := I) g x s).toCore.toCore
    tensor0SFiberNorm (I := I) g x s A = ‖A‖  := by sorry

noncomputable def tensor0SFiberNormHomeomorph
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat) :
    let metricNorm : NormedAddCommGroup (Tensor0SSpace s I x) :=
      @InnerProductSpace.Core.toNormedAddCommGroup Real
        (Tensor0SSpace s I x) _ _ _
          (tensor0SMetricData (I := I) g x s).toCore
    let metricTopology : TopologicalSpace (Tensor0SSpace s I x) :=
      metricNorm.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    let standardTopology : TopologicalSpace (Tensor0SSpace s I x) := inferInstance
    @Homeomorph (Tensor0SSpace s I x) (Tensor0SSpace s I x)
      metricTopology standardTopology := by
  classical
  let metricNorm : NormedAddCommGroup (Tensor0SSpace s I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real
      (Tensor0SSpace s I x) _ _ _
        (tensor0SMetricData (I := I) g x s).toCore
  let metricTopology : TopologicalSpace (Tensor0SSpace s I x) :=
    metricNorm.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let standardTopology : TopologicalSpace (Tensor0SSpace s I x) := inferInstance
  refine @Homeomorph.mk (Tensor0SSpace s I x) (Tensor0SSpace s I x)
    metricTopology standardTopology (Equiv.refl (Tensor0SSpace s I x)) ?_ ?_
  · let : NormedAddCommGroup (Tensor0SSpace s I x) := metricNorm
    let : InnerProductSpace.Core Real (Tensor0SSpace s I x) :=
      (tensor0SMetricData (I := I) g x s).toCore
    let : NormedSpace Real (Tensor0SSpace s I x) :=
      InnerProductSpace.Core.toNormedSpace
    let : IsBoundedSMul Real (Tensor0SSpace s I x) := inferInstance
    let : ContinuousSMul Real (Tensor0SSpace s I x) := inferInstance
    exact @LinearMap.continuous_of_finiteDimensional Real inferInstance
      (Tensor0SSpace s I x)
      inferInstance inferInstance metricTopology inferInstance inferInstance
      (Tensor0SSpace s I x)
      inferInstance inferInstance standardTopology inferInstance inferInstance
      inferInstance inferInstance inferInstance
      (LinearMap.id : Tensor0SSpace s I x →ₗ[Real] Tensor0SSpace s I x)
  · let : NormedAddCommGroup (Tensor0SSpace s I x) := metricNorm
    let : InnerProductSpace.Core Real (Tensor0SSpace s I x) :=
      (tensor0SMetricData (I := I) g x s).toCore
    let : NormedSpace Real (Tensor0SSpace s I x) :=
      InnerProductSpace.Core.toNormedSpace
    let : IsBoundedSMul Real (Tensor0SSpace s I x) := inferInstance
    let : ContinuousSMul Real (Tensor0SSpace s I x) := inferInstance
    exact @LinearMap.continuous_of_finiteDimensional Real inferInstance
      (Tensor0SSpace s I x)
      inferInstance inferInstance standardTopology inferInstance inferInstance
      (Tensor0SSpace s I x)
      inferInstance inferInstance metricTopology inferInstance inferInstance
      inferInstance inferInstance inferInstance
      (LinearMap.id : Tensor0SSpace s I x →ₗ[Real] Tensor0SSpace s I x)

theorem tensor0SFiberNorm_sq_eq_normSq0S
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A : Tensor0SSpace s I x) :
    tensor0SFiberNorm (I := I) g x s A ^ 2 =
      normSq0S (I := I) g x s A  := by sorry

@[simp] theorem normSq0S_eq_inner
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s A = inner0S (I := I) g x s A A  := by sorry

theorem normSq0S_eq_zero_iff
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s A = 0 ↔ A = 0  := by sorry

theorem inner0S_sq_le_mul
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    (inner0S (I := I) g x s A B) ^ 2 <=
      normSq0S (I := I) g x s A * normSq0S (I := I) g x s B  := by sorry

theorem normSq0S_nonneg
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A : Tensor0SSpace s I x) :
    0 <= normSq0S (I := I) g x s A  := by sorry

theorem inner0S_one_eq_cotangent
    (g : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    inner0S (I := I) g x 1 α β =
      cotangentInner (I := I) g x α β  := by sorry

def tensor0SComponent {Idx : Type*} {s : Nat} {x : M}
    (A : Tensor0SSpace s I x)
    (frame : Idx -> TangentSpace I x)
    (slots : Fin s -> Idx) : Real :=
  A (fun a => frame (slots a))

omit [FiniteDimensional ℝ E] in
@[simp] theorem tensor0SComponent_apply {Idx : Type*} {s : Nat} {x : M}
    (A : Tensor0SSpace s I x)
    (frame : Idx -> TangentSpace I x)
    (slots : Fin s -> Idx) :
    tensor0SComponent (I := I) A frame slots =
      A (fun a => frame (slots a))  := by sorry

def coordInner0S
    {Idx : Type*} [Fintype Idx] {x : M} (s : Nat)
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) : Real :=
  ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
    (∏ a : Fin s, gInv (I0 a) (J0 a)) *
      tensor0SComponent (I := I) A (fun i => basis i) I0 *
        tensor0SComponent (I := I) B (fun i => basis i) J0

private theorem sum_fin_two_fun {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α]
    (F : (Fin 2 -> Idx) -> α) :
    (∑ I0 : Fin 2 -> Idx, F I0) =
      ∑ i : Idx, ∑ j : Idx, F (fun a : Fin 2 => if a = 0 then i else j)  := by sorry

private theorem sum_fin_succ_fun {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α] (s : Nat)
    (F : (Fin (s + 1) -> Idx) -> α) :
    (∑ I0 : Fin (s + 1) -> Idx, F I0) =
      ∑ i : Idx, ∑ tail : Fin s -> Idx, F (Fin.cons i tail)  := by sorry

private theorem sum_fin_one_fun {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α]
    (F : (Fin 1 -> Idx) -> α) :
    (∑ I0 : Fin 1 -> Idx, F I0) =
      ∑ i : Idx, F (fun _ : Fin 1 => i)  := by sorry

omit [FiniteDimensional ℝ E] in
private theorem basis_repr_eq_sum_inv_inner
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Z : TangentSpace I x) (i : Idx) :
    basis.repr Z i =
      ∑ j : Idx, gInv i j * g.inner x Z (basis j)  := by sorry

private theorem hom_normSq_eq_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {W : Type*} [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (D : MetricFiberData W)
    (A : TangentSpace I x →ₗ[Real] W) :
    (MetricFiberData.hom (tangentMetricData (I := I) g x).metric D).inner A A =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * D.inner (A (basis i)) (A (basis j))  := by sorry

private theorem hom_inner_eq_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {W : Type*} [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (D : MetricFiberData W)
    (A B : TangentSpace I x →ₗ[Real] W) :
    (MetricFiberData.hom (tangentMetricData (I := I) g x).metric D).inner A B =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * D.inner (A (basis i)) (B (basis j))  := by sorry

private theorem homCLM_normSq_eq_basis
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

private theorem homCLM_inner_eq_basis
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

omit [FiniteDimensional ℝ E] in
private theorem tensor0S_curry_one_apply
    {x : M} (A : Tensor0SSpace 2 I x)
    (X Y : TangentSpace I x) :
    (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x A X)
        (fun _ : Fin 1 => Y) =
      A (fun a : Fin 2 => if a = 0 then X else Y)  := by sorry

omit [FiniteDimensional ℝ E] in
private theorem tensor0S_curry_apply_cons
    {x : M} (s : Nat) (A : Tensor0SSpace (s + 1) I x)
    (X : TangentSpace I x) (tail : Fin s -> TangentSpace I x) :
    (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x A X) tail =
      A (Fin.cons X tail)  := by sorry

theorem normSq0S_two_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A : Tensor0SSpace 2 I x) :
    normSq0S (I := I) g x 2 A =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            A (fun a : Fin 2 => if a = 0 then basis k else basis l)  := by sorry

theorem inner0S_two_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A B : Tensor0SSpace 2 I x) :
    inner0S (I := I) g x 2 A B =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            B (fun a : Fin 2 => if a = 0 then basis k else basis l)  := by sorry

private theorem inner0S_zero_eq
    (g : SmoothRiemannianMetric I M) (x : M)
    (A B : Tensor0SSpace 0 I x) :
    inner0S (I := I) g x 0 A B = A Fin.elim0 * B Fin.elim0  := by sorry

omit [FiniteDimensional ℝ E] in
private theorem coordInner0S_zero_eq
    {Idx : Type*} [Fintype Idx] {x : M}
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace 0 I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) 0 gInv A B basis =
      A Fin.elim0 * B Fin.elim0  := by sorry

omit [FiniteDimensional ℝ E] in
private theorem coordInner0S_one_eq
    {Idx : Type*} [Fintype Idx] {x : M}
    (gInv : Idx -> Idx -> Real)
    (α β : Tensor0SSpace 1 I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) 1 gInv α β basis =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * cotangentToDual (I := I) α (basis i) *
          cotangentToDual (I := I) β (basis j)  := by sorry

private theorem tensor0SMetricStep_inner_eq_coordStep
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (D : MetricFiberData (Tensor0SSpace s I x))
    (A B : Tensor0SSpace (s + 1) I x) :
    (tensor0SMetricStep (I := I) g x s D).inner A B =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          D.inner
            ((tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x A) (basis i))
            ((tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x B) (basis j))  := by sorry

omit [FiniteDimensional ℝ E] in
private theorem coordInner0S_succ_summand_eq
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
private theorem coordInner0S_succ_eq
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

theorem inner0S_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A B : Tensor0SSpace s I x) :
    inner0S (I := I) g x s A B =
      coordInner0S (I := I) (x := x) s gInv A B basis  := by sorry

theorem normSq0S_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s A =
      coordInner0S (I := I) (x := x) s gInv A A basis  := by sorry

theorem coord_normSq0S_eq_coord
    {Idx₁ Idx₂ : Type*} [Fintype Idx₁] [DecidableEq Idx₁]
    [Fintype Idx₂] [DecidableEq Idx₂]
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (basis₁ : Module.Basis Idx₁ Real (TangentSpace I x))
    (gInv₁ : Idx₁ -> Idx₁ -> Real)
    (hinv₁ : MetricInverseInBasis (I := I) g x basis₁ gInv₁)
    (basis₂ : Module.Basis Idx₂ Real (TangentSpace I x))
    (gInv₂ : Idx₂ -> Idx₂ -> Real)
    (hinv₂ : MetricInverseInBasis (I := I) g x basis₂ gInv₂)
    (A : Tensor0SSpace s I x) :
    coordInner0S (I := I) (x := x) s gInv₁ A A basis₁ =
      coordInner0S (I := I) (x := x) s gInv₂ A A basis₂  := by sorry

end

end Tensor0SBundle
end DifferentialGeometry

