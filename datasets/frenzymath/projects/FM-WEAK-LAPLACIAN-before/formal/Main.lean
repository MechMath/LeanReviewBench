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


/-!
# Morgan-Tian Ch. 1 - the Laplacian in the weak sense

This file packages the definition used in the blueprint remark
`rem:laplacian-weak-sense`.  For a locally Lipschitz function `f` and a
locally integrable function `h`, the distributional inequality `Delta f <= h`
means that

`integral f * Delta phi dvol_g <= integral h * phi dvol_g`

for every nonnegative, compactly supported smooth test function `phi`.
The Riemannian volume measure is parameterized by the additive Haar measure on
the model space, consistently with `RiemannianMeasure.lean`.
-/

open MeasureTheory
open scoped ContDiff Manifold

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [SigmaCompactSpace M] [T2Space M] [Nonempty M]

/-- **Math.** The distributional (equivalently, weak) inequality
`Delta f <= h` on the Riemannian manifold `(M, g)`.

Here `f` is locally Lipschitz, `h` is locally integrable for the Riemannian
volume measure, and the inequality is tested against every nonnegative,
compactly supported smooth function `phi`:
`integral_M f Delta phi dvol_g <= integral_M h phi dvol_g`.

The additive Haar measure `mu` fixes the normalization of the Riemannian
measure.  Rescaling it by a positive constant rescales both integrals equally.
Blueprint: `rem:laplacian-weak-sense`. -/
def WeakLaplacianLE (mu : Measure E) [mu.IsAddHaarMeasure]
    (g : RiemannianMetric I M) (f h : M → ℝ) : Prop :=
  LocallyLipschitz f ∧
    LocallyIntegrable h (riemannianMeasure (I := I) g mu) ∧
    ∀ phi : M → ℝ,
      0 ≤ phi →
      HasCompactSupport phi →
      ContMDiff I 𝓘(ℝ, ℝ) ∞ phi →
      (∫ x, f x * laplacianAt g g.leviCivitaConnection phi x
          ∂(riemannianMeasure (I := I) g mu))
        ≤ ∫ x, h x * phi x ∂(riemannianMeasure (I := I) g mu)

end MorganTianLib

end


