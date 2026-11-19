import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.StdSimplex

open Set Topology Filter
namespace DifferentialGeometry.Topology.PiecewiseLinear
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


def IsHPolytope (C : Set E) : Prop :=
  IsCompact C ∧ ∃ (ι : Type) (_ : Finite ι) (l : ι → E →ₗ[ℝ] ℝ) (c : ι → ℝ),
    C = {x | ∀ i, l i x ≤ c i}

def IsPiecewiseAffineWithinAt (f : E → F) (s : Set E) (x : E) : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (C : ι → Set E) (A : ι → E →ᵃ[ℝ] F),
    (∀ i, IsHPolytope (C i) ∧ C i ⊆ s ∧ EqOn f (A i) (C i)) ∧ (⋃ i, C i) ∈ 𝓝[s] x

def IsPiecewiseAffineOn (f : E → F) (s : Set E) : Prop :=
  ∀ x ∈ s, IsPiecewiseAffineWithinAt f s x

def IsPLHomeomorphOn (f : E → F) (P : Set E) (Q : Set F) : Prop :=
  BijOn f P Q ∧ IsPiecewiseAffineOn f P ∧ IsPiecewiseAffineOn (Function.invFunOn f P) Q

def stdSimplexBoundary (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {x | x ∈ stdSimplex ℝ (Fin (n + 1)) ∧ ∃ i, x i = 0}

def IsPLBall (n : ℕ) (P : Set E) : Prop :=
  ∃ f : (Fin (n + 1) → ℝ) → E, IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 1))) P

def IsPLSphere (n : ℕ) (P : Set E) : Prop :=
  ∃ f : (Fin (n + 2) → ℝ) → E, IsPLHomeomorphOn f (stdSimplexBoundary (n + 1)) P

def IsRadiallyInjective (p : E) (S : Set E) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ t : ℝ, 0 < t → y = p + t • (x - p) → y = x

structure IsConeBase (p : E) (L : Geometry.SimplicialComplex ℝ E) : Prop where
  notMem_space : p ∉ L.space
  indep : ∀ σ ∈ L.faces, AffineIndependent ℝ ((↑) : (insert p (σ : Set E) : Set E) → E)
  radial : IsRadiallyInjective p L.space

def coneSet (p : E) (X : Set E) : Set E :=
  {x | x = p ∨ ∃ z ∈ X, ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ x = p + s • (z - p)}

def IsPLBallPair (m k : ℕ) (P Q : Set E) : Prop :=
  ∃ (p : E) (L J : Geometry.SimplicialComplex ℝ E) (_ : IsConeBase p L),
    L.faces.Finite ∧ J.faces ⊆ L.faces ∧ IsPLSphere m L.space ∧ IsPLBall k Q ∧
      P = coneSet p L.space ∧ Q = coneSet p J.space

end DifferentialGeometry.Topology.PiecewiseLinear
