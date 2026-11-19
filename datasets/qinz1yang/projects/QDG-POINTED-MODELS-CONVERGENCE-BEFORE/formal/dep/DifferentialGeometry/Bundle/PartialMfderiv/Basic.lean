import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.VectorField

set_option autoImplicit false

open scoped Topology Manifold ContDiff

namespace DifferentialGeometry

noncomputable abbrev vderiv
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (f : M -> 𝕜) (X : (x : M) -> TangentSpace I x) : M -> 𝕜 :=
  fun x => mvfderiv (I := I) f x (X x)

@[simp] theorem vderiv_apply
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (f : M -> 𝕜) (X : (x : M) -> TangentSpace I x) (x : M) :
    vderiv (I := I) f X x = mvfderiv (I := I) f x (X x)  := by sorry

private theorem mfderiv_eq_fderivWithin_chart_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    (f : M -> Real) (x : M) (z : M) (hz : z ∈ (extChartAt I x).source)
    (hg_diffWithin : DifferentiableWithinAt Real (f ∘ (extChartAt I x).symm)
      (Set.range I) ((extChartAt I x) z)) :
    mfderiv I 𝓘(Real, Real) f z =
      (fderivWithin Real (f ∘ (extChartAt I x).symm) (Set.range I)
          ((extChartAt I x) z)).comp
        (mfderiv I 𝓘(Real, E) (extChartAt I x) z)  := by sorry

theorem vderiv_mlieBracket
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [IsManifold I 2 M]
    (X Y : (p : M) -> TangentSpace I p) (f : M -> Real) (x : M)
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% Y) x)
    (hf : ContMDiffAt I 𝓘(Real, Real) (minSmoothness Real 2) f x) :
    vderiv (I := I) f (VectorField.mlieBracket I X Y) x =
      vderiv (I := I) (vderiv (I := I) f Y) X x -
        vderiv (I := I) (vderiv (I := I) f X) Y x  := by sorry

theorem mvfderiv_apply_mlieBracket
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [IsManifold I 2 M]
    (X Y : (p : M) -> TangentSpace I p) (f : M -> Real) (x : M)
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% Y) x)
    (hf : ContMDiffAt I 𝓘(Real, Real) (minSmoothness Real 2) f x) :
    mvfderiv (I := I) f x (VectorField.mlieBracket I X Y x) =
      mvfderiv (I := I)
          (fun y : M => mvfderiv (I := I) f y (Y y)) x (X x) -
        mvfderiv (I := I)
          (fun y : M => mvfderiv (I := I) f y (X y)) x (Y x)  := by sorry

theorem contMDiff_partial_deriv_fst
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (F : C^∞⟮𝓘(ℝ, ℝ).prod I, ℝ × M; ℝ⟯) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => deriv (fun t => F (t, p.2)) p.1)  := by sorry

theorem timeDeriv_smoothAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace Real G]
    {F : Real × M -> G} {p0 : Real × M} {m n : WithTop ℕ∞}
    (hF : ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real G) n F p0)
    (hmn : m + 1 ≤ n) :
    ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real G) m
      (fun p : Real × M => deriv (fun t => F (t, p.2)) p.1) p0  := by sorry

theorem mvfderiv_const_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (c : ℝ) {f : M -> ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    mvfderiv (I := I) (fun y : M => c * f y) x =
      c • mvfderiv (I := I) f x  := by sorry

theorem mvfderiv_mul_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {f g : M -> ℝ} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x) :
    mvfderiv (I := I) (fun y : M => f y * g y) x v =
      f x * mvfderiv (I := I) g x v + g x * mvfderiv (I := I) f x v  := by sorry

theorem mdifferentiableAt_finset_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {ι : Type*} (t : Finset ι) (f : ι → M → ℝ)
    {x : M}
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (t.sum f) x  := by sorry

theorem mdiffAt_finset_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {ι : Type*} (t : Finset ι) (f : ι → M → ℝ)
    {x : M}
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (t.sum f) x  := by sorry

theorem mvfderiv_finset_sum_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {ι : Type*} (t : Finset ι) (f : ι → M → ℝ)
    {x : M} (v : TangentSpace I x)
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) x) :
    mvfderiv (I := I) (t.sum f) x v =
      t.sum (fun i => mvfderiv (I := I) (f i) x v)  := by sorry

theorem mvfderiv_finset_sum_apply_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {ι : Type*} (t : Finset ι) (f : ι → M → ℝ)
    {x : M} (v : TangentSpace I x)
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) x) :
    mvfderiv (I := I) (fun y => ∑ i ∈ t, f i y) x v =
      ∑ i ∈ t, mvfderiv (I := I) (f i) x v  := by sorry

theorem mvfderiv_finset_sum_mul_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {ι : Type*} (t : Finset ι) (U B : ι -> M -> ℝ)
    {x : M} (v : TangentSpace I x)
    (hU : ∀ i ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (U i) x)
    (hB : ∀ i ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (B i) x) :
    mvfderiv (I := I) (fun y : M => ∑ i ∈ t, U i y * B i y) x v =
      ∑ i ∈ t,
        (U i x * mvfderiv (I := I) (B i) x v +
          B i x * mvfderiv (I := I) (U i) x v)  := by sorry

theorem mvfderiv_finset_sum_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {ι : Type*} (t : Finset ι) (F : ι -> M -> ℝ)
    {x : M} (v : TangentSpace I x)
    (hF : ∀ i ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (F i) x) :
    mvfderiv (I := I) (fun y : M => ∑ i ∈ t, F i y) x v =
      ∑ i ∈ t, mvfderiv (I := I) (F i) x v  := by sorry

theorem mvfderiv_finset_sum_sum_mul_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {ι κ : Type*} (s : Finset ι) (t : Finset κ) (U B : ι -> κ -> M -> ℝ)
    {x : M} (v : TangentSpace I x)
    (hU : ∀ i ∈ s, ∀ j ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (U i j) x)
    (hB : ∀ i ∈ s, ∀ j ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (B i j) x) :
    mvfderiv (I := I) (fun y : M => ∑ i ∈ s, ∑ j ∈ t, U i j y * B i j y) x v =
      ∑ i ∈ s, ∑ j ∈ t,
        (U i j x * mvfderiv (I := I) (B i j) x v +
          B i j x * mvfderiv (I := I) (U i j) x v)  := by sorry

theorem mvfderiv_apply_contMDiff
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (f : M -> 𝕜) (hf : ContMDiff I 𝓘(𝕜, 𝕜) ∞ f)
    (X : ContMDiffSection I E ∞ (TangentSpace I : M -> Type _)) :
    ContMDiff I 𝓘(𝕜, 𝕜) ∞
      (fun p : M => mvfderiv (I := I) f p (X p))  := by sorry

theorem mvfderiv_apply_contMDiffAt
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {f : M -> 𝕜} {x₀ : M}
    (hf : ContMDiffAt I 𝓘(𝕜, 𝕜) ∞ f x₀)
    (X : ContMDiffSection I E ∞ (TangentSpace I : M -> Type _)) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) ∞
      (fun p : M => mvfderiv (I := I) f p (X p)) x₀  := by sorry

theorem contMDiffAt_partial_mvfderiv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {F : Real × M -> Real} {X : (x : M) -> TangentSpace I x}
    {t : Real} {x : M} {m : WithTop ℕ∞} (hm : m ≤ (∞ : WithTop ℕ∞))
    (hF : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) (m + 1) F (t, x))
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E))
      (∞ : WithTop ℕ∞) (T% X) x) :
    ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) m
      (fun p : Real × M =>
        mvfderiv (I := I) (fun y : M => F (p.1, y)) p.2 (X p.2))
      (t, x)  := by sorry

theorem contMDiffAt_partial_mvfderiv_apply_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {F : Real × M -> Real} {X : (x : M) -> TangentSpace I x}
    {t : Real} {x : M}
    (hF : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real)
      (3 : WithTop ℕ∞) F (t, x))
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E))
      (∞ : WithTop ℕ∞) (T% X) x) :
    ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real)
      (2 : WithTop ℕ∞)
      (fun p : Real × M =>
        mvfderiv (I := I) (fun y : M => F (p.1, y)) p.2 (X p.2))
      (t, x)  := by sorry

theorem contMDiffAt_partial_mvfderiv_apply_infty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {F : Real × M -> Real} {X : (x : M) -> TangentSpace I x}
    {t : Real} {x : M}
    (hF : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real)
      (∞ : WithTop ℕ∞) F (t, x))
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E))
      (∞ : WithTop ℕ∞) (T% X) x) :
    ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun p : Real × M =>
        mvfderiv (I := I) (fun y : M => F (p.1, y)) p.2 (X p.2))
      (t, x)  := by sorry

theorem contMDiffWithinAt_partial_mvfderiv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {J : Set Real} {u : Set M} (hu : IsOpen u)
    {F : Real × M -> Real} {X : (x : M) -> TangentSpace I x}
    {t : Real} {x : M} (ht : t ∈ J) (hx : x ∈ u)
    (hF : ContMDiffWithinAt (𝓘(Real, Real).prod I) 𝓘(Real, Real)
      (∞ : WithTop ℕ∞) F (J ×ˢ u) (t, x))
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E))
      (∞ : WithTop ℕ∞) (T% X) x) :
    ContMDiffWithinAt (𝓘(Real, Real).prod I) 𝓘(Real, Real)
      (∞ : WithTop ℕ∞)
      (fun p : Real × M =>
        mvfderiv (I := I) (fun y : M => F (p.1, y)) p.2 (X p.2))
      (J ×ˢ u) (t, x)  := by sorry

end DifferentialGeometry

