import Mathlib

open MeasureTheory Measure Set Filter Module Matrix Function Bundle Manifold

open scoped ENNReal NNReal Topology ContDiff Manifold Bundle

noncomputable section

namespace BilinearForm





abbrev Form (𝕜 : Type*) [CommSemiring 𝕜]
    (V : Type*) [AddCommMonoid V] [Module 𝕜 V] :=
  LinearMap.BilinForm 𝕜 V

end BilinearForm

namespace BilinearForm



variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {V : Type*} [AddCommGroup V] [Module 𝕜 V]

def IsPosDef (B : Form 𝕜 V) : Prop :=
  ∀ v ≠ 0, 0 < B v v

end BilinearForm

namespace BilinearForm



variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {V : Type*} [AddCommGroup V] [Module 𝕜 V]

omit [IsStrictOrderedRing 𝕜] in


theorem IsPosDef.nondegenerate {B : Form 𝕜 V} (hB : IsPosDef B) :
    (B : LinearMap.BilinForm 𝕜 V).Nondegenerate := by sorry

end BilinearForm

namespace BilinearForm



variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {V : Type*} [AddCommGroup V] [Module 𝕜 V]
variable [FiniteDimensional 𝕜 V]

noncomputable def toDualEquiv {B : Form 𝕜 V} (hB : IsPosDef B) :
    V ≃ₗ[𝕜] (V →ₗ[𝕜] 𝕜) :=
  LinearMap.BilinForm.toDual B hB.nondegenerate

end BilinearForm

namespace BilinearForm



variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {V : Type*} [AddCommGroup V] [Module 𝕜 V]
variable [FiniteDimensional 𝕜 V]

noncomputable def riesz {B : Form 𝕜 V} (hB : IsPosDef B)
    (φ : V →ₗ[𝕜] 𝕜) : V :=
  (toDualEquiv hB).symm φ

end BilinearForm

namespace Riemannian





abbrev RiemannianMetric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] : Type _ :=
  Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)

end Riemannian

namespace Riemannian



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

structure SmoothVectorField (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] where
  

  toFun : Π y : M, TangentSpace I y
  

  smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
    (fun y => (⟨y, toFun y⟩ : TangentBundle I M))

end Riemannian

namespace Riemannian.SmoothVectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

instance : CoeFun (SmoothVectorField I M) fun _ => Π y : M, TangentSpace I y := ⟨toFun⟩

end Riemannian.SmoothVectorField

namespace Riemannian.SmoothVectorField



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def zero : SmoothVectorField I M where
  toFun := fun _ => 0
  smooth := by sorry

end Riemannian.SmoothVectorField

namespace Riemannian.SmoothVectorField



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def add (X Y : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun y => X y + Y y
  smooth := by sorry

end Riemannian.SmoothVectorField

namespace Riemannian.SmoothVectorField



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def neg (X : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun y => -X y
  smooth := by sorry

end Riemannian.SmoothVectorField

namespace Riemannian.SmoothVectorField



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def sub (X Y : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun y => X y - Y y
  smooth := by sorry

end Riemannian.SmoothVectorField

namespace Riemannian.SmoothVectorField



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def constSMul (a : ℝ) (X : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun y => a • X y
  smooth := by sorry

end Riemannian.SmoothVectorField

namespace Riemannian.SmoothVectorField



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def smul (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun y => f y • X y
  smooth := by sorry

end Riemannian.SmoothVectorField

namespace Riemannian.SmoothVectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

instance : Zero (SmoothVectorField I M) := ⟨zero⟩

instance : Add (SmoothVectorField I M) := ⟨add⟩

instance : Neg (SmoothVectorField I M) := ⟨neg⟩

instance : Sub (SmoothVectorField I M) := ⟨sub⟩

instance : SMul ℝ (SmoothVectorField I M) := ⟨constSMul⟩

end Riemannian.SmoothVectorField

namespace Riemannian



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def SmoothVectorField.dir (X : SmoothVectorField I M) (f : M → ℝ) (p : M) : ℝ :=
  mfderiv I 𝓘(ℝ, ℝ) f p (X p)

end Riemannian

namespace Riemannian



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def dirTangent (f : M → ℝ) {p : M} (v : TangentSpace I p) : ℝ :=
  mfderiv I 𝓘(ℝ, ℝ) f p v

end Riemannian

namespace Riemannian



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

structure AffineConnection (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] where
  

  cov : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M
  

  add_left : ∀ X Y Z : SmoothVectorField I M, cov (X + Y) Z = cov X Z + cov Y Z
  

  smul_left : ∀ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
      (X Z : SmoothVectorField I M),
      cov (SmoothVectorField.smul f hf X) Z = SmoothVectorField.smul f hf (cov X Z)
  

  add_right : ∀ X Y Z : SmoothVectorField I M, cov X (Y + Z) = cov X Y + cov X Z
  

  leibniz : ∀ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
      (X Y : SmoothVectorField I M) (p : M),
      (cov X (SmoothVectorField.smul f hf Y)) p
        = f p • (cov X Y) p + (SmoothVectorField.dir X f p) • (Y p)

end Riemannian

namespace Riemannian.RiemannianMetric



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def metricInner (g : RiemannianMetric I M)
    (x : M) (V W : TangentSpace I x) : ℝ :=
  g.inner x V W

end Riemannian.RiemannianMetric

namespace Riemannian.RiemannianMetric



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private noncomputable def toBilinForm (g : RiemannianMetric I M) (x : M) :
    BilinearForm.Form ℝ E :=
  LinearMap.mk₂ ℝ
    (fun v w => g.inner x v w)
    (fun v₁ v₂ w => by sorry)
    (fun c v w => by sorry)
    (fun v w₁ w₂ => (g.inner x v).map_add w₁ w₂)
    (fun c v w => (g.inner x v).map_smul c w)

end Riemannian.RiemannianMetric

namespace Riemannian.RiemannianMetric



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
private theorem toBilinForm_isPosDef (g : RiemannianMetric I M) (x : M) :
    BilinearForm.IsPosDef (g.toBilinForm x) := by sorry

end Riemannian.RiemannianMetric

namespace Riemannian.RiemannianMetric



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def metricRiesz (g : RiemannianMetric I M) (x : M)
    (φ : TangentSpace I x →L[ℝ] ℝ) :
    TangentSpace I x :=
  BilinearForm.riesz (V := E) (g.toBilinForm_isPosDef x)
    ((φ : TangentSpace I x →ₗ[ℝ] ℝ))

end Riemannian.RiemannianMetric

namespace Riemannian



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def RiemannianMetric.koszulRHSraw (g : RiemannianMetric I M)
    (X Y : SmoothVectorField I M) (σ : Π q : M, TangentSpace I q) (p : M) : ℝ :=
  X.dir (fun q => g.metricInner q (Y q) (σ q)) p
    + Y.dir (fun q => g.metricInner q (σ q) (X q)) p
    - dirTangent (fun q => g.metricInner q (X q) (Y q)) (σ p)
    - g.metricInner p (VectorField.mlieBracket I X.toFun σ p) (Y p)
    - g.metricInner p (VectorField.mlieBracket I Y.toFun σ p) (X p)
    - g.metricInner p (VectorField.mlieBracket I X.toFun Y.toFun p) (σ p)

end Riemannian

namespace Riemannian



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem RiemannianMetric.koszulRHSraw_tensorialAt (g : RiemannianMetric I M)
    (X Y : SmoothVectorField I M) (p : M) :
    TensorialAt I E (fun σ => g.koszulRHSraw X Y σ p) p := by sorry

end Riemannian

namespace Riemannian



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def RiemannianMetric.koszulCovec [FiniteDimensional ℝ E]
    (g : RiemannianMetric I M) (X Y : SmoothVectorField I M) (p : M) :
    TangentSpace I p →L[ℝ] ℝ :=
  TensorialAt.mkHom (fun σ => g.koszulRHSraw X Y σ p) p
    (g.koszulRHSraw_tensorialAt X Y p)

end Riemannian

namespace Riemannian



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def RiemannianMetric.koszulDualSection [FiniteDimensional ℝ E]
    (g : RiemannianMetric I M) (X Y : SmoothVectorField I M) (p : M) :
    TangentSpace I p :=
  g.metricRiesz p ((1 / 2 : ℝ) • g.koszulCovec X Y p)

end Riemannian

namespace Riemannian



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem RiemannianMetric.koszulDualSection_contMDiffAt [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    (X Y : SmoothVectorField I M) (p : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (⟨y, g.koszulDualSection X Y y⟩ : TangentBundle I M)) p := by sorry

end Riemannian

namespace Riemannian



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def RiemannianMetric.leviCivitaCovField [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    (A B : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun p => g.koszulDualSection B A p
  smooth := by sorry

end Riemannian

namespace Riemannian



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def RiemannianMetric.leviCivitaConnection [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M) :
    AffineConnection I M where
  cov := fun A B => g.leviCivitaCovField A B
  add_left := by sorry
  smul_left := by sorry
  add_right := by sorry
  leibniz := by sorry

end Riemannian

namespace Riemannian



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [CompleteSpace E] in


theorem exists_smoothVectorField_eq [FiniteDimensional ℝ E] [SigmaCompactSpace M]
    [T2Space M] (p : M) (v : TangentSpace I p) :
    ∃ Z : SmoothVectorField I M, Z p = v := by sorry

end Riemannian

namespace Riemannian.Tensor



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartBasisVecFiber (α : M) (i : Fin (Module.finrank ℝ E)) (b : M) :
    TangentSpace I b :=
  (trivializationAt E (TangentSpace I) α).symm b ((Module.finBasis ℝ E) i)

end Riemannian.Tensor

namespace Riemannian.Tensor



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartGramMatrix (g : RiemannianMetric I M) (α : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j =>
    g.inner x
      (chartBasisVecFiber (I := I) α i x)
      (chartBasisVecFiber (I := I) α j x)

end Riemannian.Tensor

namespace MorganTianLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

abbrev RiemannianMetric (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Type _ :=
  Riemannian.RiemannianMetric I M

end MorganTianLib

namespace MorganTianLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]

noncomputable def extendVector (p : M) (v : TangentSpace I p) :
    SmoothVectorField I M :=
  Classical.choose (exists_smoothVectorField_eq p v)

end MorganTianLib

namespace MorganTianLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def hessian (nabla : AffineConnection I M) (f : M → ℝ)
    (X Y : SmoothVectorField I M) (p : M) : ℝ :=
  X.dir (Y.dir f) p - (nabla.cov X Y).dir f p

end MorganTianLib

namespace MorganTianLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]

noncomputable def hessianAt (nabla : AffineConnection I M) (f : M → ℝ) (p : M)
    (v w : TangentSpace I p) : ℝ :=
  hessian nabla f (extendVector p v) (extendVector p w) p

end MorganTianLib

namespace MorganTianLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]

noncomputable def laplacianAt (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (f : M → ℝ) (p : M) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ∑ i, hessianAt nabla f p (stdOrthonormalBasis ℝ (TangentSpace I p) i)
    (stdOrthonormalBasis ℝ (TangentSpace I p) i)

end MorganTianLib

namespace MorganTianLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M]

def chartVolumeDensity (g : RiemannianMetric I M) (α : M) (y : E) : ℝ :=
  Real.sqrt ((Riemannian.Tensor.chartGramMatrix (I := I) g α ((extChartAt I α).symm y)).det)

end MorganTianLib

namespace MorganTianLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M]

def chartMeasure (g : RiemannianMetric I M) (μ : Measure E) (α : M) : Measure M :=
  Measure.map (extChartAt I α).symm
    ((μ.restrict (extChartAt I α).target).withDensity
      (fun y => ENNReal.ofReal (chartVolumeDensity (I := I) g α y)))

end MorganTianLib

namespace MorganTianLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M]
variable (μ : Measure E) [μ.IsAddHaarMeasure]
variable [SecondCountableTopology M] [Nonempty M]

theorem exists_countable_chart_cover :
    ∃ c : ℕ → M, (⋃ n, (extChartAt I (c n)).source) = univ := by sorry

end MorganTianLib

namespace MorganTianLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M]
variable (μ : Measure E) [μ.IsAddHaarMeasure]
variable [SecondCountableTopology M] [Nonempty M]

def chartCover : ℕ → M :=
  Classical.choose (exists_countable_chart_cover (I := I) (M := M))

end MorganTianLib

namespace MorganTianLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M]
variable (μ : Measure E) [μ.IsAddHaarMeasure]
variable [SecondCountableTopology M] [Nonempty M]

def chartPiece (n : ℕ) : Set M :=
  disjointed (fun k => (extChartAt I (chartCover (I := I) (M := M) k)).source) n

end MorganTianLib

namespace MorganTianLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M]
variable (μ : Measure E) [μ.IsAddHaarMeasure]
variable [SecondCountableTopology M] [Nonempty M]

def riemannianMeasure (g : RiemannianMetric I M) (μ : Measure E) : Measure M :=
  Measure.sum fun n =>
    (chartMeasure (I := I) g μ (chartCover (I := I) (M := M) n)).restrict
      (chartPiece (I := I) (M := M) n)

end MorganTianLib



namespace Riemannian.Tensor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
 [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
 {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
 {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
 [I.Boundaryless] 
  [MeasurableSpace E] [BorelSpace E] 
 
def chartInvGramMatrix (g : RiemannianMetric I M) (α : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  (chartGramMatrix (I := I) g α x)⁻¹
end Riemannian.Tensor



namespace Riemannian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open Riemannian.Tensor
def partialDeriv (i : Fin (Module.finrank ℝ E)) (u : E → ℝ) (y : E) : ℝ :=
  fderiv ℝ u y ((Module.finBasis ℝ E) i)

end Riemannian

namespace Riemannian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open Riemannian.Tensor
def chartGramOnE (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => chartGramMatrix (I := I) g α ((extChartAt I α).symm y) i j

end Riemannian

namespace Riemannian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open Riemannian.Tensor
def chartChristoffel (g : RiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) k l *
      (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
       partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
       partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y)

end Riemannian

namespace Riemannian.Geodesic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartCoord (i : Fin (Module.finrank ℝ E)) (v : E) : ℝ :=
  (Module.finBasis ℝ E).repr v i

end Riemannian.Geodesic

namespace Riemannian.Geodesic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartChristoffelContraction (g : RiemannianMetric I M) (α : M)
    (v w : E) (y : E) : E :=
  ∑ k : Fin (Module.finrank ℝ E),
    (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j k y *
          chartCoord (E := E) i v * chartCoord (E := E) j w) •
      Module.finBasis ℝ E k

end Riemannian.Geodesic

namespace Riemannian.Geodesic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartLocalCurve (γ : ℝ → M) (t : ℝ) : ℝ → E :=
  fun s => extChartAt I (γ t) (γ s)

end Riemannian.Geodesic

namespace Riemannian.Geodesic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def HasGeodesicEquationAt (g : RiemannianMetric I M) (γ : ℝ → M)
    (t : ℝ) : Prop :=
  ∃ v a : E,
    HasDerivAt (chartLocalCurve (I := I) γ t) v t ∧
    (∀ᶠ s in nhds t, HasDerivAt (chartLocalCurve (I := I) γ t)
        (deriv (chartLocalCurve (I := I) γ t) s) s) ∧
    HasDerivAt (fun s => deriv (chartLocalCurve (I := I) γ t) s) a t ∧
    a + chartChristoffelContraction (I := I) g (γ t) v v
        (extChartAt I (γ t) (γ t)) = 0

end Riemannian.Geodesic

namespace Riemannian.Geodesic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def IsGeodesicOn (g : RiemannianMetric I M) (γ : ℝ → M)
    (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasGeodesicEquationAt (I := I) g γ t

end Riemannian.Geodesic


open Metric Riemannian Riemannian.Tensor Riemannian.Geodesic


namespace Riemannian
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
abbrev DCLieBracket (X Y : SmoothVectorField I M) (p : M) : TangentSpace I p :=
  VectorField.mlieBracket I X.toFun Y.toFun p
end
end Riemannian


namespace Riemannian.AffineConnection
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
def IsSymmetric (nabla : AffineConnection I M) : Prop :=
  ∀ (X Y : SmoothVectorField I M) (p : M),
    (nabla.cov X Y) p - (nabla.cov Y X) p = DCLieBracket X Y p
end
end Riemannian.AffineConnection


namespace Riemannian.AffineConnection
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
def IsMetricCompatible (g : RiemannianMetric I M) (nabla : AffineConnection I M) :
    Prop :=
  ∀ (X Y Z : SmoothVectorField I M) (p : M),
    X.dir (fun q => g.metricInner q (Y q) (Z q)) p
      = g.metricInner p ((nabla.cov X Y) p) (Z p)
        + g.metricInner p (Y p) ((nabla.cov X Z) p)
end
end Riemannian.AffineConnection


namespace Riemannian.AffineConnection
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
def IsLeviCivita (g : RiemannianMetric I M) (nabla : AffineConnection I M) : Prop :=
  nabla.IsSymmetric ∧ nabla.IsMetricCompatible g
end
end Riemannian.AffineConnection


namespace Riemannian.RiemannianMetric
section
variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*}
variable [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
def IsRiemannianDist (g : RiemannianMetric I M) : Prop :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  IsRiemannianManifold I M
end
end Riemannian.RiemannianMetric


namespace Riemannian
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
noncomputable def bracketField (X Y : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun p => DCLieBracket X Y p
  smooth := by sorry
end
end Riemannian


namespace Riemannian.AffineConnection
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable (nabla : AffineConnection I M)
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
noncomputable def curvature (X Y Z : SmoothVectorField I M) : SmoothVectorField I M :=
  nabla.cov Y (nabla.cov X Z) - nabla.cov X (nabla.cov Y Z)
    + nabla.cov (bracketField X Y) Z
end
end Riemannian.AffineConnection


namespace Riemannian.AffineConnection
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable (nabla : AffineConnection I M)
variable [I.Boundaryless] (g : RiemannianMetric I M)
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
def curvatureForm (X Y Z T : SmoothVectorField I M) (p : M) : ℝ :=
  g.metricInner p ((nabla.curvature X Y Z) p) (T p)
end
end Riemannian.AffineConnection


namespace Riemannian
section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
structure IsAlgCurvatureForm (B : V → V → V → V → ℝ) : Prop where
  

  add_left : ∀ x₁ x₂ y z t, B (x₁ + x₂) y z t = B x₁ y z t + B x₂ y z t
  

  smul_left : ∀ (a : ℝ) x y z t, B (a • x) y z t = a * B x y z t
  

  antisymm₁₂ : ∀ x y z t, B x y z t = - B y x z t
  

  antisymm₃₄ : ∀ x y z t, B x y z t = - B x y t z
  

  bianchi : ∀ x y z t, B x y z t + B y z x t + B z x y t = 0
end
end Riemannian


namespace Riemannian
section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
def rieszInvEquiv (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] V :=
  ((InnerProductSpace.toDual ℝ V).toLinearEquiv ≪≫ₗ LinearMap.toContinuousLinearMap.symm).symm
end
end Riemannian


namespace Riemannian
section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
def bilinTrace (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : ℝ :=
  LinearMap.trace ℝ V ((rieszInvEquiv V).toLinearMap ∘ₗ β)
end
end Riemannian


namespace Riemannian
section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
def ricciBilinAux {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B) (x y : V) :
    V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => B x z y w)
    (by sorry) (by sorry) (by sorry) (by sorry)
end
end Riemannian


namespace Riemannian
section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
def ricciForm {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B) (x y : V) : ℝ :=
  bilinTrace (ricciBilinAux hB x y)
end
end Riemannian


namespace Riemannian.Geodesic
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
def IsGeodesic (g : RiemannianMetric I M) (γ : ℝ → M) : Prop :=
  ∀ t : ℝ, HasGeodesicEquationAt (I := I) g γ t
end
end Riemannian.Geodesic


namespace Riemannian.Geodesic
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
def chartReading (α : M) (γ : ℝ → M) : ℝ → E :=
  fun τ => extChartAt I α (γ τ)
end
end Riemannian.Geodesic


namespace Riemannian.Geodesic
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
theorem exists_global_geodesic (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompleteSpace M] (p : M) (v : TangentSpace I p) :
    ∃ γ : ℝ → M, γ 0 = p ∧
      HasDerivAt (chartReading (I := I) p γ) (v : E) 0 ∧
      Continuous γ ∧ IsGeodesic (I := I) g γ := by sorry
end
end Riemannian.Geodesic


namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
def globalGeodesic (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) (v : TangentSpace I p) : ℝ → M :=
  Classical.choose (Riemannian.Geodesic.exists_global_geodesic (I := I) g hg p v)
end
end MorganTianLib


namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
def expMapGlobal (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) (v : TangentSpace I p) : M :=
  globalGeodesic (I := I) g hg p v 1
end
end MorganTianLib


namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
def IsMinimizingUpTo (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (v : TangentSpace I p) (t : ℝ) : Prop :=
  dist p (globalGeodesic (I := I) g hg p v t) = Real.sqrt (g.metricInner p v v) * t
end
end MorganTianLib


namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
def minimizingTimes (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (v : TangentSpace I p) : Set ℝ :=
  {t : ℝ | 0 ≤ t ∧ IsMinimizingUpTo (I := I) g hg p v t}
end
end MorganTianLib


namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
def cutTime (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (v : TangentSpace I p) : ℝ≥0∞ :=
  ⨆ t ∈ minimizingTimes (I := I) g hg p v, ENNReal.ofReal t
end
end MorganTianLib


namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
noncomputable def curvatureFormAt (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) (v w z t : TangentSpace I p) : ℝ :=
  nabla.curvatureForm g (extendVector p v) (extendVector p w)
    (extendVector p z) (extendVector p t) p
end
end MorganTianLib


namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
theorem isAlgCurvatureForm_curvatureFormAt [I.Boundaryless]
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (hLC : nabla.IsLeviCivita g) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    IsAlgCurvatureForm (curvatureFormAt g nabla p) := by sorry
end
end MorganTianLib


namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
noncomputable def ricciAt [I.Boundaryless] (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g) (p : M)
    (v w : TangentSpace I p) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ricciForm (isAlgCurvatureForm_curvatureFormAt g nabla hLC p) v w
end
end MorganTianLib


namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
def gpBilin (g : RiemannianMetric I M) (p : M) : LinearMap.BilinForm ℝ E :=
  LinearMap.mk₂ ℝ (fun v w : E => g.metricInner p v w)
    (by sorry) (by sorry) (by sorry) (by sorry)
end
end MorganTianLib


namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
theorem gpBilin_isSymm (g : RiemannianMetric I M) (p : M) :
    LinearMap.IsSymm (gpBilin (I := I) g p) := by sorry
end
end MorganTianLib


namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
def metricOrthoBasis₀ (g : RiemannianMetric I M) (p : M) :
    Basis (Fin (Module.finrank ℝ E)) ℝ E :=
  Classical.choose (LinearMap.BilinForm.exists_orthogonal_basis (gpBilin_isSymm (I := I) g p))
end
end MorganTianLib


namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
theorem metricOrthoBasis₀_self_pos (g : RiemannianMetric I M) (p : M)
    (i : Fin (Module.finrank ℝ E)) :
    0 < gpBilin (I := I) g p (metricOrthoBasis₀ (I := I) g p i) (metricOrthoBasis₀ (I := I) g p i) := by sorry
end
end MorganTianLib


namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
def metricOrthoUnit (g : RiemannianMetric I M) (p : M) (i : Fin (Module.finrank ℝ E)) : ℝˣ :=
  Units.mk0 (Real.sqrt (gpBilin (I := I) g p (metricOrthoBasis₀ (I := I) g p i)
      (metricOrthoBasis₀ (I := I) g p i)))⁻¹
    (inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (metricOrthoBasis₀_self_pos (I := I) g p i))))
end
end MorganTianLib


namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
def metricOrthoBasis (g : RiemannianMetric I M) (p : M) :
    Basis (Fin (Module.finrank ℝ E)) ℝ E :=
  (metricOrthoBasis₀ (I := I) g p).unitsSMul (metricOrthoUnit (I := I) g p)
end
end MorganTianLib


namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
def gpEuclideanEquiv (g : RiemannianMetric I M) (p : M) : 𝔼 ≃ₗ[ℝ] E :=
  (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis.equiv
    (metricOrthoBasis (I := I) g p) (Equiv.refl _)
end
end MorganTianLib


namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
def gpHaar (g : RiemannianMetric I M) (p : M) : Measure E :=
  Measure.map (gpEuclideanEquiv (I := I) g p) volume
end
end MorganTianLib


namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
def expRiemannianJacobian (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (v : E) : ℝ :=
  |(fderiv ℝ (fun w : E => extChartAt I (expMapGlobal (I := I) g hg p v)
      (expMapGlobal (I := I) g hg p w)) v).det|
    * chartVolumeDensity (I := I) g (expMapGlobal (I := I) g hg p v)
        (extChartAt I (expMapGlobal (I := I) g hg p v) (expMapGlobal (I := I) g hg p v))
end
end MorganTianLib


namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
def transportedJacobian (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) : 𝔼 → ℝ :=
  fun x => {y : 𝔼 | 1 < cutTime (I := I) g hg p (gpEuclideanEquiv (I := I) g p y)}.indicator
    (fun y => expRiemannianJacobian (I := I) g hg p (gpEuclideanEquiv (I := I) g p y)) x
end
end MorganTianLib

namespace MorganTianLib
noncomputable def snK (k r : ℝ) : ℝ :=
  if k = 0 then r else Real.sinh (Real.sqrt k * r) / Real.sqrt k
end MorganTianLib


namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
def modelDensity (k : ℝ) (x : E) : ℝ :=
  if ‖x‖ = 0 then 1 else (snK k ‖x‖ / ‖x‖) ^ (finrank ℝ E - 1)
end
end MorganTianLib


namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
def modelBallVolume (k : ℝ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in ball (0 : E) r,
    ENNReal.ofReal (modelDensity (E := E) k x) ∂μ
end
end MorganTianLib


namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [T2Space (TangentBundle I M)]
  [CompleteSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
theorem bishop_gromov_manifold_ratio
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [ConnectedSpace M]
    (p : M) {k R : ℝ} (hk : 0 ≤ k) (hR : 0 < R)
    (_hcompact : IsCompact (closure (Metric.ball p R)))
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hLC : (g.leviCivitaConnection).IsLeviCivita g)
    (hric : ∀ x ∈ Metric.closedBall p R, ∀ v : TangentSpace I x,
      -(((Module.finrank ℝ E : ℝ) - 1) * k) * g.metricInner x v v
        ≤ ricciAt g g.leviCivitaConnection hLC x v v)
    (hjac : Measurable (transportedJacobian (I := I) g hg p)) :
    AntitoneOn
      (fun r =>
        riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r) /
          modelBallVolume (volume : Measure 𝔼) k r)
      (Ioo 0 R) := by sorry
end
end MorganTianLib


namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [T2Space (TangentBundle I M)]
  [CompleteSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
def gpHaarOriginDensity (g : RiemannianMetric I M) (p : M) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt ((chartGramMatrix (I := I) g p p).det))
end
end MorganTianLib


namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [T2Space (TangentBundle I M)]
  [CompleteSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
structure BishopGromovManifoldProducers
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [ConnectedSpace M] (p : M)
    (R : ℝ) : Prop where
  transportedJacobian_measurable :
    Measurable (transportedJacobian (I := I) g hg p)
  small_radius_normalization :
    Tendsto
      (fun r =>
        riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r) /
          modelBallVolume (volume : Measure 𝔼) 0 r)
      (𝓝[>] (0 : ℝ)) (𝓝 (gpHaarOriginDensity (I := I) g p))
  flat_model_power_identification :
    ∃ C : ℝ≥0∞, 0 < C ∧ C ≠ ⊤ ∧
      ∀ r ∈ Ioo (0 : ℝ) R,
        modelBallVolume (volume : Measure 𝔼) 0 r = C * ENNReal.ofReal (r ^ Module.finrank ℝ E)
end
end MorganTianLib


namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [T2Space (TangentBundle I M)]
  [CompleteSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
theorem bishop_gromov_manifold_with_producers
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [ConnectedSpace M]
    (p : M) {k R : ℝ} (hk : 0 ≤ k) (hR : 0 < R)
    (hcompact : IsCompact (closure (Metric.ball p R)))
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hLC : (g.leviCivitaConnection).IsLeviCivita g)
    (hric : ∀ x ∈ Metric.closedBall p R, ∀ v : TangentSpace I x,
      -(((Module.finrank ℝ E : ℝ) - 1) * k) * g.metricInner x v v
        ≤ ricciAt g g.leviCivitaConnection hLC x v v)
    (hric0 : ∀ x ∈ Metric.closedBall p R, ∀ v : TangentSpace I x,
      0 ≤ ricciAt g g.leviCivitaConnection hLC x v v)
    (hCnorm : gpHaarOriginDensity (I := I) g p = 1)
    (hprod : BishopGromovManifoldProducers (I := I) g hg p R) :
    AntitoneOn
      (fun r =>
        riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r) /
          modelBallVolume (volume : Measure 𝔼) k r)
      (Ioo 0 R) ∧
    Tendsto
      (fun r =>
        riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r) /
          modelBallVolume (volume : Measure 𝔼) 0 r)
      (𝓝[>] (0 : ℝ)) (𝓝 1) ∧
    AntitoneOn
      (fun r =>
        riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r) /
          ENNReal.ofReal (r ^ Module.finrank ℝ E))
      (Ioo 0 R) := by sorry
end
end MorganTianLib

end

open Riemannian Riemannian.Tensor Riemannian.Geodesic Filter Set MeasureTheory Measure Metric Module Bundle Manifold
open scoped ContDiff Manifold Topology Bundle Matrix ENNReal NNReal
noncomputable section
namespace MorganTianLib
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
theorem expMapGlobal_localDiffeo_of_minimizing
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {v : E} (hv0 : (v : TangentSpace I p) ≠ 0)
    (hmin : IsMinimizingUpTo (I := I) g hg p (v : TangentSpace I p) 1)
    {t₀ : ℝ} (ht₀0 : 0 < t₀) (ht₀1 : t₀ < 1) :
    IsMinimizingUpTo (I := I) g hg p (v : TangentSpace I p) t₀ ∧
      (∃ (ζ : M) (D : E ≃L[ℝ] E),
        expMapGlobal (I := I) g hg p ((t₀ • v : E) : TangentSpace I p) ∈ (chartAt H ζ).source ∧
        HasStrictFDerivAt (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w))
          (D : E →L[ℝ] E) (t₀ • v)) ∧
      (∃ U ∈ 𝓝 ((t₀ • v : E)), Set.InjOn (expMapGlobal (I := I) g hg p) U) := by sorry
end
end MorganTianLib
end
