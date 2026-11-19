import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.Model.Tensor0S
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.Model.TensorRS
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.InducedConnection
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.Model.Smoothness
import dep.DifferentialGeometry.Bundle.Section
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

namespace CovariantDerivative

open Bundle
open scoped Manifold ContDiff

def ContMDiffCovariantDerivativeLocally
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (k : WithTop ℕ∞) : Prop :=
  ∀ ⦃u : Set M⦄, IsOpen u → ContMDiffCovariantDerivativeOn E k cov.toFun u

theorem ContMDiffCovariantDerivative.contMDiff_apply
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [VectorBundle 𝕜 E (TangentSpace I : M → Type _)]
    {n : WithTop ℕ∞}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : ContMDiffCovariantDerivative cov n)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (Y : ContMDiffSection I E (n + 1) (TangentSpace I : M → Type _)) :
    ContMDiff I (I.prod 𝓘(𝕜, E)) n
      (fun p : M =>
        (⟨p, (cov (fun q : M => Y q) p) (X p)⟩ :
          TotalSpace E (TangentSpace I : M → Type _)))  := by sorry

end CovariantDerivative

