import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import dep.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Defs
import dep.DifferentialGeometry.Bundle.Section

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
lemma SmoothRiemannianMetric.eq_of_inner_eq
    (g : SmoothRiemannianMetric I M) {x : M} {v w : TangentSpace I x}
    (h : ∀ ζ : TangentSpace I x, g.inner x v ζ = g.inner x w ζ) : v = w  := by sorry

variable
  {cov : (Π x : M, TangentSpace I x) →
    (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)}
  {g : SmoothRiemannianMetric I M}

@[reducible] def directionalDeriv (f : M → ℝ) (x : M) (v : TangentSpace I x) : ℝ :=
  (mfderiv I 𝓘(ℝ) f x) v

@[reducible] def directionalDerivAt (f : M → ℝ) (x : M) (v : TangentSpace I x) : ℝ :=
  directionalDeriv (I := I) f x v

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
@[simp] lemma directionalDeriv_eq (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    directionalDeriv (I := I) f x v = (mfderiv I 𝓘(ℝ) f x) v  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
@[simp] lemma directionalDerivAt_eq (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    directionalDerivAt (I := I) f x v = (mfderiv I 𝓘(ℝ) f x) v  := by sorry

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
theorem koszul_identity_on
    {s : Set M}
    (hMC : IsMetricCompatibleOn cov g s)
    (hTF : ∀ ⦃X Y : Π x : M, TangentSpace I x⦄ ⦃x : M⦄,
      MDiffAt (T% X) x → MDiffAt (T% Y) x → x ∈ s →
      cov Y x (X x) - cov X x (Y x) = VectorField.mlieBracket I X Y x)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (hxs : x ∈ s) :
    2 * g.inner x (cov Y x (X x)) (Z x) =
      directionalDeriv (I := I) (fun b => g.inner b (Y b) (Z b)) x (X x)
      + directionalDeriv (I := I) (fun b => g.inner b (X b) (Z b)) x (Y x)
      - directionalDeriv (I := I) (fun b => g.inner b (X b) (Y b)) x (Z x)
      + g.inner x (VectorField.mlieBracket I X Y x) (Z x)
      - g.inner x (VectorField.mlieBracket I X Z x) (Y x)
      - g.inner x (VectorField.mlieBracket I Y Z x) (X x)  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem koszul_identity
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (htor : cov.torsion = 0)
    (hMC : IsMetricCompatible cov g)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    2 * g.inner x (cov.toFun Y x (X x)) (Z x) =
      directionalDeriv (I := I) (fun b => g.inner b (Y b) (Z b)) x (X x)
      + directionalDeriv (I := I) (fun b => g.inner b (X b) (Z b)) x (Y x)
      - directionalDeriv (I := I) (fun b => g.inner b (X b) (Y b)) x (Z x)
      + g.inner x (VectorField.mlieBracket I X Y x) (Z x)
      - g.inner x (VectorField.mlieBracket I X Z x) (Y x)
      - g.inner x (VectorField.mlieBracket I Y Z x) (X x)  := by sorry

omit [SigmaCompactSpace M] in
theorem koszul_local_uniqueness
    {s : Set M}
    {cov₁ cov₂ : (Π x : M, TangentSpace I x) →
      (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)}
    (hTF₁ : ∀ ⦃X Y : Π x : M, TangentSpace I x⦄ ⦃x : M⦄,
      MDiffAt (T% X) x → MDiffAt (T% Y) x → x ∈ s →
      cov₁ Y x (X x) - cov₁ X x (Y x) = VectorField.mlieBracket I X Y x)
    (hTF₂ : ∀ ⦃X Y : Π x : M, TangentSpace I x⦄ ⦃x : M⦄,
      MDiffAt (T% X) x → MDiffAt (T% Y) x → x ∈ s →
      cov₂ Y x (X x) - cov₂ X x (Y x) = VectorField.mlieBracket I X Y x)
    (hMC₁ : IsMetricCompatibleOn cov₁ g s)
    (hMC₂ : IsMetricCompatibleOn cov₂ g s)
    {X Y : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hxs : x ∈ s) :
    cov₁ Y x (X x) = cov₂ Y x (X x)  := by sorry

omit [SigmaCompactSpace M] in
theorem koszul_levi_civita_unique_of_torsionFree_metricCompatible
    (cov₁ cov₂ : CovariantDerivative I E (TangentSpace I : M → Type _))
    (htor₁ : cov₁.torsion = 0) (htor₂ : cov₂.torsion = 0)
    (hMC₁ : IsMetricCompatible cov₁ g) (hMC₂ : IsMetricCompatible cov₂ g)
    {Y : Π x : M, TangentSpace I x} {x : M} (hY : MDiffAt (T% Y) x)
    (v : TangentSpace I x) :
    cov₁.toFun Y x v = cov₂.toFun Y x v  := by sorry

end Connection
end Geometry
end DifferentialGeometry

