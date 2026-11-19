import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.Connection.Smooth
import dep.DifferentialGeometry.Bundle.Section
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.InducedConnection
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

namespace DifferentialGeometry
namespace TensorLieDeriv

noncomputable section


open Bundle Set IsManifold ContinuousLinearMap VectorField Filter
    DifferentialGeometry.Tensor0SBundle Function
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I n M]
variable {x x₀ : M} {s : Set M}

variable [CompleteSpace 𝕜]

section TangentCovariantDerivative

variable [IsManifold I 1 M]

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
theorem covariantDeriv_vectorField_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)) :
    ContMDiff I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, covariantDerivVectorField (I := I) cov (fun q => X q) (fun q => Y q) p⟩ :
          TotalSpace E (TangentSpace I : M → Type _)))  := by sorry

noncomputable def covSection
    [VectorBundle 𝕜 E (TangentSpace I : M → Type _)]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov (∞ : WithTop ℕ∞))
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)) :
    ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) where
  toFun := fun p : M => (cov (fun q : M => Y q) p) (X p)
  contMDiff_toFun := by
    simpa [covariantDerivVectorField] using
      covariantDeriv_vectorField_contMDiff (I := I) cov hcov X Y

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
@[simp] theorem covSection_apply
    [VectorBundle 𝕜 E (TangentSpace I : M → Type _)]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov (∞ : WithTop ℕ∞))
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (p : M) :
    covSection (I := I) cov hcov X Y p = (cov (fun q : M => Y q) p) (X p)  := by sorry

noncomputable def tangentFieldModelInChart (x₀ : M)
    (V : (x : M) → TangentSpace I x) (y : E) : E :=
  (trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearMapAt 𝕜
    ((extChartAt I x₀).symm y) (V ((extChartAt I x₀).symm y))

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
theorem tangentFieldModelInChart_tangentConstInChart_apply_of_mem
    (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target) (v : E) :
    tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀
        (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ v) y = v  := by sorry

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
theorem tangentConstInChart_self_continuousLinearMapAt
    (x : M) (v : TangentSpace I x) :
    tangentConstInChart (𝕜 := 𝕜) (I := I) x
        ((trivializationAt E (TangentSpace I : M → Type _) x).continuousLinearMapAt
          𝕜 x v) x =
      v  := by sorry

omit [CompleteSpace 𝕜] in
theorem tangentField_eq_sum_modelCoord_tangentConst_eventually_of_mem
    (x₀ : M) (V : (x : M) → TangentSpace I x) {p₀ : M}
    (hp₀ : p₀ ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet) :
    V =ᶠ[𝓝 p₀]
      fun p : M =>
        ∑ i : Fin (Module.finrank 𝕜 E),
          (Module.finBasis 𝕜 E).coord i
              (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
                (extChartAt I x₀ p)) •
            tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
              ((Module.finBasis 𝕜 E) i) p  := by sorry

omit [CompleteSpace 𝕜] in
theorem tangentField_eq_sum_modelCoord_tangentConst_eventually
    (x₀ : M) (V : (x : M) → TangentSpace I x) :
    V =ᶠ[𝓝 x₀]
      fun p : M =>
        ∑ i : Fin (Module.finrank 𝕜 E),
          (Module.finBasis 𝕜 E).coord i
              (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
                (extChartAt I x₀ p)) •
            tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
              ((Module.finBasis 𝕜 E) i) p  := by sorry

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
omit [IsManifold I n M] in
lemma tangentConstInChart_contMDiffOn_baseSet (x₀ : M) (v : E)
    [IsManifold I (n + 1) M] :
    CMDiff[(trivializationAt E (TangentSpace I) x₀).baseSet] n
      (T% (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ v :
        (p : M) → TangentSpace I p))  := by sorry

end TangentCovariantDerivative

end

end TensorLieDeriv

end DifferentialGeometry
namespace CovariantDerivative
open DifferentialGeometry

open Bundle
open scoped Manifold ContDiff

theorem smoothSections_cov_contMDiffAt_one
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [hM2 : IsManifold I 2 M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : ContMDiffCovariantDerivativeLocally cov (1 : WithTop ℕ∞))
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    ContMDiffAt I (I.prod 𝓘(𝕜, E)) (1 : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, (cov (fun q : M => Y q) p) (X p)⟩ :
          TotalSpace E (TangentSpace I : M → Type _))) x  := by sorry

theorem tangentConst_cov_mdiffAt
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : ContMDiffCovariantDerivativeLocally cov (1 : WithTop ℕ∞))
    {x : M} (v w : TangentSpace I x) :
    MDiffAt
      (T% (fun p : M =>
        (cov (TensorLieDeriv.tangentConstInChart (𝕜 := 𝕜) (I := I) x
            ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt 𝕜 x w)) p)
          ((TensorLieDeriv.tangentConstInChart (𝕜 := 𝕜) (I := I) x
            ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt 𝕜 x v)) p))) x  := by sorry

end CovariantDerivative

