import dep.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Defs
import dep.DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import dep.DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import dep.DifferentialGeometry.Geometry.Operator.Laplacian.Rough
import dep.DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.Basic
import dep.DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.Pairing
import dep.DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.ConnectionProduct
import dep.DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.Moving
import dep.DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.Smoothness
import dep.DifferentialGeometry.Geometry.Connection.RicciIdentity.OneForm.Realization
import dep.DifferentialGeometry.Geometry.Connection.RicciIdentity.Tensor0S.Realization
import dep.DifferentialGeometry.Geometry.Connection.RicciIdentity.Tensor0S.Formula
import dep.DifferentialGeometry.Geometry.Connection.RicciIdentity.MixedComponents
import dep.DifferentialGeometry.Geometry.Connection.LocalFrameRegularity
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.Regularity.TotalNabla0S
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.ConnectionDifference
open DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Operator


open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


def differential1FormFun (u : M -> Real) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
  dualToCotangent (I := I) (mvfderiv (I := I) u x).toLinearMap

def duField (u : M -> Real) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
  differential1FormFun (I := I) u x


def DuFieldRealizes (u : M -> Real)
    (du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1) : Prop :=
  ∀ x : M, du x = duField (I := I) u x

private theorem duFun_contMDiff
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u) :
    letI := tensor0SBundleTopology (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) 1
    letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞))
    ContMDiff I (I.prod 𝓘(Real, Tensor0SModel 1 Real E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, differential1FormFun (I := I) u p⟩ :
          TotalSpace (Tensor0SModel 1 Real E)
            (fun p : M => Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 p)))  := by sorry

noncomputable def duSec
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u) :
    OneFormSection (I := I) (M := M) := by
  letI := tensor0SBundleTopology (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) 1
  exact ⟨fun x : M => differential1FormFun (I := I) u x,
    duFun_contMDiff (I := I) u hu⟩

@[simp]
theorem duSec_apply
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u)
    (x : M) :
    duSec (I := I) u hu x = differential1FormFun (I := I) u x  := by sorry

theorem duSec_realizes
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u) :
    DuFieldRealizes (I := I) u (duSec (I := I) u hu)  := by sorry

theorem differential1FormFun_apply_eq_mvfderiv
    (u : M -> Real) (x : M) (v : TangentSpace I x) :
    differential1FormFun (I := I) u x (fun _ : Fin 1 => v) =
      mvfderiv (I := I) u x v  := by sorry

theorem dphi_apply_smooth
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u)
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _)) :
    ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun p : M => mvfderiv (I := I) u p (Y p))  := by sorry

theorem dphi_apply_mdiffAt
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u)
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun p : M => mvfderiv (I := I) u p (Y p)) x  := by sorry

theorem differential1FormFun_apply_eq_inner_gradientFun
    (g : SmoothRiemannianMetric I M) (u : M -> Real)
    (x : M) (v : TangentSpace I x) :
    differential1FormFun (I := I) u x (fun _ : Fin 1 => v) =
      g.inner x (gradientFun (I := I) g u x) v  := by sorry

noncomputable def nablaDuAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
  nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 cov X du x

def hessianAt
    (Hess : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  Hess x

def HessianRealizesNablaDuAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1)
    (Hess : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M) : Prop :=
  ∀ (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
      (Y : TangentSpace I x),
    Hess x (vec2 (X x) Y) =
      nablaDuAt (I := I) cov X du x (fun _ : Fin 1 => Y)

theorem nablaDu_eq_hessian
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1)
    (Hess : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M)
    (hHess : HessianRealizesNablaDuAt (I := I) cov du Hess x)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Y : TangentSpace I x) :
    nablaDuAt (I := I) cov X du x (fun _ : Fin 1 => Y) =
      Hess x (vec2 (X x) Y)  := by sorry

theorem hess_of_nabla
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1)
    (Hess : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M)
    (h : NablaOneFormRealizesAt (I := I) cov du Hess x) :
    HessianRealizesNablaDuAt (I := I) cov du Hess x  := by sorry

noncomputable def hessianSec
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u) :
    TwoTensorSection (I := I) (M := M) :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    1 cov (duSec (I := I) u hu)
    (totalNabla0S_regularity (E := E) (H := H) (I := I) (M := M)
      1 cov hcov (duSec (I := I) u hu))

@[simp]
theorem hessianSec_apply
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u)
    (x : M) :
    hessianSec (I := I) cov hcov u hu x =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        1 cov (duSec (I := I) u hu) x  := by sorry

theorem hessianSec_nabla
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u) :
    NablaOneFormRealizes (I := I) cov (duSec (I := I) u hu)
      (hessianSec (I := I) cov hcov u hu)  := by sorry

theorem hess_sub_conn
    [T2Space M]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (hcov' : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov'
      (∞ : WithTop ℕ∞))
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u)
    (x : M) :
    hessianSec (I := I) cov hcov u hu x -
        hessianSec (I := I) cov' hcov' u hu x =
      -bilinearCovectorComp (I := I)
        (CovariantDerivative.difference cov cov' x) (duSec (I := I) u hu x)  := by sorry

theorem hessianSec_realizesAt
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u)
    (x : M) :
    HessianRealizesNablaDuAt (I := I) cov (duSec (I := I) u hu)
      (fun y : M => hessianSec (I := I) cov hcov u hu y) x  := by sorry

theorem hessSec_inner_cov
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible
      (I := I) cov g)
    (f : M -> Real) (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f)
    (x : M) (v w : TangentSpace I x) :
    hessianSec (I := I) cov hcov f hf x (vec2 (I := I) v w) =
      g.inner x ((cov (fun y : M => gradientFun (I := I) g f y) x) v) w  := by sorry

noncomputable def nablaHessSec
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u) :
    Tensor0SSection (I := I) (M := M) 3 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    2 cov (hessianSec (I := I) cov hcov u hu)
    (totalNabla0S_regularity (E := E) (H := H) (I := I) (M := M)
      2 cov hcov (hessianSec (I := I) cov hcov u hu))

@[simp]
theorem nablaHess_apply
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u)
    (x : M) :
    nablaHessSec (I := I) cov hcov u hu x =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov (hessianSec (I := I) cov hcov u hu) x  := by sorry

theorem nablaHess_realizes
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u)
    (x : M) :
    Nabla2OneFormRealizesAt (I := I) cov (duSec (I := I) u hu)
      (hessianSec (I := I) cov hcov u hu) x
      (nablaHessSec (I := I) cov hcov u hu x)  := by sorry

theorem freezeFirst_elim0 {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    freezeFirstTwo0S (I := I) T Fin.elim0 = T  := by sorry

theorem traceFirstTwo_elim0
    (g : SmoothRiemannianMetric I M) {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    metricTraceFirstTwo0SAt (I := I) g T Fin.elim0 =
      metricTracePair0SAt (I := I) g T  := by sorry

def scalarLapTraceAt
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Real :=
  metricTracePair0SAt (I := I) g hessF

@[simp]
theorem scalarLapTraceAt_eq_pair
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    scalarLapTraceAt (I := I) g hessF =
      metricTracePair0SAt (I := I) g hessF  := by sorry

theorem scalarLapTraceAt_eq_firstTwo
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    scalarLapTraceAt (I := I) g hessF =
      metricTraceFirstTwo0SAt (I := I) g hessF Fin.elim0  := by sorry

def ScalarLaplacianRealizesTraceAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (f : M -> Real)
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Prop :=
  laplacian (I := I) cov g f x =
    metricTraceFirstTwo0SAt (I := I) g hessF Fin.elim0

def ScalarLaplacianRealizesTraceAtInBasis
    {Idx : Type*} [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (f : M -> Real)
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Prop :=
  laplacian (I := I) cov g f x =
    metricTrace0S2InBasis (I := I) basis gInv hessF Fin.elim0

theorem scalar_laplacian_trace_of_hessian
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (f : M -> Real)
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (htrace :
      laplacian (I := I) cov g f x =
        metricTraceFirstTwo0SAt (I := I) g hessF Fin.elim0) :
    ScalarLaplacianRealizesTraceAt (I := I) cov g f hessF  := by sorry

theorem scalar_laplacian_trace_of_pair
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (f : M -> Real)
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (htrace :
      laplacian (I := I) cov g f x =
        scalarLapTraceAt (I := I) g hessF) :
    ScalarLaplacianRealizesTraceAt (I := I) cov g f hessF  := by sorry

theorem ScalarLaplacianRealizesTraceAt.eq_trace
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (f : M -> Real)
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (h : ScalarLaplacianRealizesTraceAt (I := I) cov g f hessF) :
    laplacian (I := I) cov g f x =
      scalarLapTraceAt (I := I) g hessF  := by sorry

theorem lapTrace_of_slots
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (f : M -> Real)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x)
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hlap : ScalarLaplacianRealizesTraceAt (I := I) cov g f hessF)
    (hslots :
      ∀ X Y : TangentSpace I x,
        T (metricTraceInput (I := I) X Y tail) =
          hessF (vec2 (I := I) X Y)) :
    metricTraceFirstTwo0SAt (I := I) g T tail =
      laplacian (I := I) cov g f x  := by sorry

theorem ScalarLaplacianRealizesTraceAt.toInBasis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (f : M -> Real)
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (h : ScalarLaplacianRealizesTraceAt (I := I) cov g f hessF) :
    ScalarLaplacianRealizesTraceAtInBasis (I := I) cov g basis gInv f hessF  := by sorry

def SmoothBasisFieldsAt
    {Idx : Type*}
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) : Prop :=
  ∀ i : Idx, X i x = basis i

private theorem hessian_component_eq_inner_cov_gradient
    {Idx : Type*}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (f : M -> Real)
    (duSec : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1)
    (hessF : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hdu : DuFieldRealizes (I := I) f duSec)
    (hHess : HessianRealizesNablaDuAt (I := I) cov duSec hessF x)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x)
    (i j : Idx) :
    hessF x (vec2 (I := I) (basis i) (basis j)) =
      g.inner x ((cov (fun y : M => gradientFun (I := I) g f y) x) (basis i))
        (basis j)  := by sorry

theorem scalarLaplacianRealizesTraceAt_of_nablaDu
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (f : M -> Real)
    (duSec : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1)
    (hessF : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hdu : DuFieldRealizes (I := I) f duSec)
    (hHess : HessianRealizesNablaDuAt (I := I) cov duSec hessF x)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    ScalarLaplacianRealizesTraceAt (I := I) cov g f (hessF x)  := by sorry

theorem scalarLapTraceAt_of_nablaDu
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (f : M -> Real)
    (duSec : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1)
    (hessF : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hdu : DuFieldRealizes (I := I) f duSec)
    (hHess : HessianRealizesNablaDuAt (I := I) cov duSec hessF x)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov g f x =
      scalarLapTraceAt (I := I) g (hessF x)  := by sorry

theorem scalarLap_canon
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    {x : M}
    (f : M -> Real)
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    ScalarLaplacianRealizesTraceAt (I := I) cov g f
      (hessianSec (I := I) cov hcov f hf x)  := by sorry

theorem scalarLap_smooth
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    {x : M}
    (f : M -> Real)
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f) :
    ScalarLaplacianRealizesTraceAt (I := I) cov g f
      (hessianSec (I := I) cov hcov f hf x)  := by sorry

theorem lap_sub_conn
    [T2Space M]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (hcov' : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov'
      (∞ : WithTop ℕ∞))
    (g g' : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible
      (I := I) cov g)
    (hmc' : DifferentialGeometry.Geometry.Connection.IsMetricCompatible
      (I := I) cov' g')
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u)
    (x : M) :
    laplacian (I := I) cov g u x - laplacian (I := I) cov' g' u x =
      (scalarLapTraceAt (I := I) g
          (hessianSec (I := I) cov' hcov' u hu x) -
        scalarLapTraceAt (I := I) g'
          (hessianSec (I := I) cov' hcov' u hu x)) -
      scalarLapTraceAt (I := I) g
        (bilinearCovectorComp (I := I)
          (CovariantDerivative.difference cov cov' x) (duSec (I := I) u hu x))  := by sorry

theorem lapTrace_nablaSec
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    (f : M -> Real)
    (duSec : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1)
    (hessF : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (hdu : DuFieldRealizes (I := I) f duSec)
    (hHess : ∀ y : M, HessianRealizesNablaDuAt (I := I) cov duSec hessF y)
    (hgrad : ∀ y : M, MDiffAt (T% fun z : M => gradientFun (I := I) g f z) y) :
    ∀ y : M,
      laplacian (I := I) cov g f y =
        scalarLapTraceAt (I := I) g (hessF y)  := by sorry

end DifferentialGeometry.Geometry.Operator

