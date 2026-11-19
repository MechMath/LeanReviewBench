import dep.DifferentialGeometry.Tensor.RSTensor.Coordinates.BundleBasis
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.Connection.Smooth
import dep.DifferentialGeometry.Bundle.TangentSpace
import Mathlib.Geometry.Manifold.VectorBundle.Hom

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

attribute [local instance] Fintype.ofFinite Classical.propDecidable

open Bundle
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem covariantDerivative_finset_sum_tangent
    {ι : Type*} (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (t : Finset ι) (σ : ι → (x : M) → TangentSpace I x)
    {x : M} (v : TangentSpace I x)
    (hσ : ∀ i, MDiffAt (T% (σ i)) x) :
    (cov (t.sum σ) x) v = t.sum (fun i => (cov (σ i) x) v)  := by sorry

omit [CompleteSpace E] in
theorem covariantDerivative_localFrame_coeff_eq
    {ι : Type*} [Finite ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet) (hσ : MDiffAt (T% σ) x) (i k : ι) :
    e.localFrameCoeff I b k x
        ((cov σ x) (e.localFrame b i x)) =
      mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b k)) σ)
        x (e.localFrame b i x) +
        ∑ j : ι,
          e.localFrameCoeff I b j x (σ x) *
            e.localFrameCoeff I b k x
              ((cov (e.localFrame b j) x) (e.localFrame b i x))  := by sorry

omit [CompleteSpace E] in
theorem covariantDerivative_localFrame_coeff_eq_along
    {ι : Type*} [Finite ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet) (hσ : MDiffAt (T% σ) x)
    (v : TangentSpace I x) (k : ι) :
    e.localFrameCoeff I b k x ((cov σ x) v) =
      mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b k)) σ) x v +
        ∑ j : ι,
          e.localFrameCoeff I b j x (σ x) *
            e.localFrameCoeff I b k x
              ((cov (e.localFrame b j) x) v)  := by sorry

noncomputable def homModelCoeff
    {ι : Type*} (b : Module.Basis ι Real E) (i k : ι) :
    (E →L[Real] E) →ₗ[Real] Real where
  toFun A := b.coord k (A (b i))
  map_add' A B := by simp
  map_smul' c A := by simp

noncomputable def localHomCoeff
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E) (i k : ι) (x : M) :
    (TangentSpace I x →L[Real] TangentSpace I x) →ₗ[Real] Real :=
  (homModelCoeff (E := E) b i k).comp
    ((e.continuousLinearMap (RingHom.id Real) e).linearMapAt Real x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem localHomCoeff_apply
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {x : M} (hx : x ∈ e.baseSet)
    (A : TangentSpace I x →L[Real] TangentSpace I x) (i k : ι) :
    localHomCoeff (I := I) e b i k x A =
      e.localFrameCoeff I b k x (A (e.localFrame b i x))  := by sorry

omit [CompleteSpace E] in
theorem homLocalFrameCoeff_eq_localHomCoeff
    {ι : Type*} [Finite ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {x : M} (hx : x ∈ e.baseSet)
    (A : TangentSpace I x →L[Real] TangentSpace I x) (i k : ι) :
    (e.continuousLinearMap (RingHom.id Real) e).localFrameCoeff I
        (continuousLinearMapHomBasis (𝕜 := Real) b b) (k, i) x A =
      localHomCoeff (I := I) e b i k x A  := by sorry

omit [CompleteSpace E] in
theorem covariantDerivative_localHomCoeff_eq
    {ι : Type*} [Finite ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet) (hσ : MDiffAt (T% σ) x) (i k : ι) :
    localHomCoeff (I := I) e b i k x (cov σ x) =
      mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b k)) σ)
        x (e.localFrame b i x) +
        ∑ j : ι,
          e.localFrameCoeff I b j x (σ x) *
            e.localFrameCoeff I b k x
              ((cov (e.localFrame b j) x) (e.localFrame b i x))  := by sorry

omit [CompleteSpace E] in
theorem covariantDerivative_localHomCoeff_eventuallyEq
    {ι : Type*} [Finite ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet) (hσ : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y) (i k : ι) :
    (fun y : M => localHomCoeff (I := I) e b i k y (cov σ y)) =ᶠ[𝓝 x]
      fun y : M =>
        mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b k)) σ)
          y (e.localFrame b i y) +
          ∑ j : ι,
            e.localFrameCoeff I b j y (σ y) *
              e.localFrameCoeff I b k y
                ((cov (e.localFrame b j) y) (e.localFrame b i y))  := by sorry

omit [CompleteSpace E] in
theorem covariantDerivative_localHomCoeff_contMDiffAt
    {ι : Type*} [Finite ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet) (hσ : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (i k : ι)
    (hderiv : ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b k)) σ)
          y (e.localFrame b i y)) x)
    (hcoeff : ∀ j : ι, ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M => e.localFrameCoeff I b j y (σ y)) x)
    (hchristoffel : ∀ j : ι, ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        e.localFrameCoeff I b k y
          ((cov (e.localFrame b j) y) (e.localFrame b i y))) x) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M => localHomCoeff (I := I) e b i k y (cov σ y)) x  := by sorry

omit [CompleteSpace E] in
theorem covariantDerivative_localHomCoeff_contMDiffAt_one
    {ι : Type*} [Finite ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet) (hσ : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (i k : ι)
    (hderiv : ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
      (fun y : M =>
        mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b k)) σ)
          y (e.localFrame b i y)) x)
    (hcoeff : ∀ j : ι, ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
      (fun y : M => e.localFrameCoeff I b j y (σ y)) x)
    (hchristoffel : ∀ j : ι, ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
      (fun y : M =>
        e.localFrameCoeff I b k y
          ((cov (e.localFrame b j) y) (e.localFrame b i y))) x) :
    ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
      (fun y : M => localHomCoeff (I := I) e b i k y (cov σ y)) x  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem mvfderiv_apply_contMDiffAt_of_section
    {f : M -> Real} {X : (p : M) -> TangentSpace I p} {x₀ : M}
    (hf : ContMDiffAt I 𝓘(Real, Real) ∞ f x₀)
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
      (fun p : M => (⟨p, X p⟩ :
        TotalSpace E (TangentSpace I : M -> Type _))) x₀) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun p : M => mvfderiv (I := I) f p (X p)) x₀  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem mvfderiv_apply_contMDiffAt_of_section_one
    {f : M -> Real} {X : (p : M) -> TangentSpace I p} {x₀ : M}
    (hf : ContMDiffAt I 𝓘(Real, Real) (2 : WithTop ℕ∞) f x₀)
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
      (fun p : M => (⟨p, X p⟩ :
        TotalSpace E (TangentSpace I : M -> Type _))) x₀) :
    ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
      (fun p : M => mvfderiv (I := I) f p (X p)) x₀  := by sorry

omit [CompleteSpace E] in
theorem localFrameCoeff_extDeriv_contMDiffAt
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet)
    (hσ : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞ (T% σ) x)
    (i k : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b k)) σ)
          y (e.localFrame b i y)) x  := by sorry

omit [CompleteSpace E] in
theorem localFrameCoeff_extDeriv_contMDiffAt_one
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet)
    (hσ : ContMDiffAt I (I.prod 𝓘(Real, E)) (2 : WithTop ℕ∞) (T% σ) x)
    (i k : ι) :
    ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
      (fun y : M =>
        mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b k)) σ)
          y (e.localFrame b i y)) x  := by sorry

omit [CompleteSpace E] in
theorem covariantDerivative_localHomCoeff_contMDiffAt_of_section
    {ι : Type*} [Finite ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet)
    (hσdiff : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (hσ : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞ (T% σ) x)
    (i k : ι)
    (hchristoffel : ∀ j : ι, ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        e.localFrameCoeff I b k y
          ((cov (e.localFrame b j) y) (e.localFrame b i y))) x) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M => localHomCoeff (I := I) e b i k y (cov σ y)) x  := by sorry

omit [CompleteSpace E] in
theorem covariantDerivative_localHomCoeff_contMDiffAt_of_section_one
    {ι : Type*} [Finite ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet)
    (hσdiff : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (hσ : ContMDiffAt I (I.prod 𝓘(Real, E)) (2 : WithTop ℕ∞) (T% σ) x)
    (i k : ι)
    (hchristoffel : ∀ j : ι, ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        e.localFrameCoeff I b k y
          ((cov (e.localFrame b j) y) (e.localFrame b i y))) x) :
    ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
      (fun y : M => localHomCoeff (I := I) e b i k y (cov σ y)) x  := by sorry

omit [CompleteSpace E] in
theorem covariantDerivative_homSection_contMDiffAt_of_coeff
    {ι : Type*} [Finite ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet)
    (hσdiff : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (hσ : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞ (T% σ) x)
    (hchristoffel : ∀ i k j : ι, ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        e.localFrameCoeff I b k y
          ((cov (e.localFrame b j) y) (e.localFrame b i y))) x) :
    ContMDiffAt I (I.prod 𝓘(Real, E →L[Real] E)) ∞
      (fun y : M =>
        (⟨y, cov σ y⟩ :
          TotalSpace (E →L[Real] E)
            (fun y : M => TangentSpace I y →L[Real] TangentSpace I y))) x  := by sorry

omit [CompleteSpace E] in
theorem covariantDerivative_homSection_contMDiffAt_of_coeff_one
    {ι : Type*} [Finite ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet)
    (hσdiff : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (hσ : ContMDiffAt I (I.prod 𝓘(Real, E)) (2 : WithTop ℕ∞) (T% σ) x)
    (hchristoffel : ∀ i k j : ι, ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        e.localFrameCoeff I b k y
          ((cov (e.localFrame b j) y) (e.localFrame b i y))) x) :
    ContMDiffAt I (I.prod 𝓘(Real, E →L[Real] E)) (1 : WithTop ℕ∞)
      (fun y : M =>
        (⟨y, cov σ y⟩ :
          TotalSpace (E →L[Real] E)
            (fun y : M => TangentSpace I y →L[Real] TangentSpace I y))) x  := by sorry

end DifferentialGeometry

