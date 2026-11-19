import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

namespace DifferentialGeometry.Tensor0SBundle

noncomputable section

structure MetricFiberData (V : Type*) [AddCommGroup V] [Module Real V]
    [FiniteDimensional Real V] where
  flat : V ≃ₗ[Real] Module.Dual Real V
  symm : forall v w : V, flat v w = flat w v
  nonneg : forall v : V, 0 <= flat v v

namespace MetricFiberData

variable {V : Type*} [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]

omit [FiniteDimensional ℝ V] in
private theorem dual_finrank_eq :
    Module.finrank Real V = Module.finrank Real (Module.Dual Real V)  := by sorry

def ofFlat
    (flat : V →ₗ[Real] Module.Dual Real V)
    (hinj : Function.Injective flat)
    (hsymm : forall v w : V, flat v w = flat w v)
    (hnonneg : forall v : V, 0 <= flat v v) :
    MetricFiberData V where
  flat := LinearMap.linearEquivOfInjective flat hinj dual_finrank_eq
  symm := hsymm
  nonneg := hnonneg

def ofBilinForm (B : LinearMap.BilinForm ℝ V) (hsymm : B.IsSymm)
    (hpos : B.toQuadraticMap.PosDef) : MetricFiberData V :=
  ofFlat B
    (LinearMap.ker_eq_bot.mp
      (LinearMap.separatingLeft_iff_ker_eq_bot.mp
        (LinearMap.BilinForm.separatingLeft_of_anisotropic hpos.anisotropic)))
    hsymm.eq hpos.nonneg

def inner (D : MetricFiberData V) (v w : V) : Real :=
  D.flat v w

@[simp] theorem ofBilinForm_inner (B : LinearMap.BilinForm ℝ V) (hsymm : B.IsSymm)
    (hpos : B.toQuadraticMap.PosDef) (v w : V) :
    (ofBilinForm B hsymm hpos).inner v w = B v w  := by sorry

def sharp (D : MetricFiberData V) : Module.Dual Real V ≃ₗ[Real] V :=
  D.flat.symm

@[simp] theorem inner_apply (D : MetricFiberData V) (v w : V) :
    D.inner v w = D.flat v w  := by sorry

theorem inner_comm (D : MetricFiberData V) (v w : V) :
    D.inner v w = D.inner w v  := by sorry

theorem inner_nonneg (D : MetricFiberData V) (v : V) :
    0 <= D.inner v v  := by sorry

theorem inner_self_eq_zero_iff (D : MetricFiberData V) (v : V) :
    D.inner v v = 0 ↔ v = 0  := by sorry

theorem inner_pos_of_ne_zero (D : MetricFiberData V) {v : V} (hv : v ≠ 0) :
    0 < D.inner v v  := by sorry

@[reducible] def toCore (D : MetricFiberData V) : InnerProductSpace.Core Real V where
  inner := fun v w => D.inner v w
  conj_inner_symm := by
    intro x y
    exact D.symm y x
  re_inner_nonneg := by
    intro x
    simpa using D.inner_nonneg x
  add_left := by
    intro x y z
    simp [MetricFiberData.inner, map_add]
  smul_left := by
    intro x y r
    simp [MetricFiberData.inner, smul_eq_mul]
  definite := by
    intro x hx
    exact (D.inner_self_eq_zero_iff x).1 (by simpa using hx)

theorem toCore_inner (D : MetricFiberData V) (v w : V) :
    letI : InnerProductSpace.Core Real V := D.toCore
    letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup
    letI : InnerProductSpace Real V :=
      @InnerProductSpace.ofCore Real V _ _ _ D.toCore.toCore
    Inner.inner Real v w = D.inner v w  := by sorry

def orthogonal (D : MetricFiberData V) (W : Submodule Real V) : Submodule Real V :=
  LinearMap.BilinForm.orthogonal D.flat.toLinearMap W

@[simp] theorem mem_orthogonal
    (D : MetricFiberData V) (W : Submodule Real V) (v : V) :
    v ∈ D.orthogonal W ↔ ∀ w ∈ W, D.inner w v = 0  := by sorry

def IsSymmetric (D : MetricFiberData V) (A : V →ₗ[Real] V) : Prop :=
  ∀ v w, D.inner (A v) w = D.inner v (A w)

theorem trace_pos_of_isSymmetric_of_nonneg_of_ne_zero
    (D : MetricFiberData V) (A : V →ₗ[Real] V)
    (hAsymm : D.IsSymmetric A)
    (hAnonneg : ∀ v : V, 0 ≤ D.inner (A v) v)
    (hAne : A ≠ 0) :
    0 < LinearMap.trace Real V A  := by sorry

theorem IsSymmetric.range_eq_orthogonal_ker
    {D : MetricFiberData V} {A : V →ₗ[Real] V} (hA : D.IsSymmetric A) :
    A.range = D.orthogonal A.ker  := by sorry

variable {W : Type*} [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]

theorem map_orthogonal_of_inner_eq
    (DV : MetricFiberData V) (DW : MetricFiberData W)
    (e : V ≃ₗ[Real] W)
    (hinner : ∀ v w, DW.inner (e v) (e w) = DV.inner v w)
    (K : Submodule Real V) :
    Submodule.map e.toLinearMap (DV.orthogonal K) =
      DW.orthogonal (Submodule.map e.toLinearMap K)  := by sorry

noncomputable def submoduleProjection
    (D : MetricFiberData V) (W : Submodule Real V) : V →ₗ[Real] W := by
  let addV : AddCommGroup V := inferInstance
  let modV : Module Real V := inferInstance
  letI : InnerProductSpace.Core Real V := D.toCore
  letI : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real V _ addV modV D.toCore
  letI : AddCommGroup V := addV
  letI : Module Real V := modV
  letI : InnerProductSpace Real V :=
    @InnerProductSpace.ofCore Real V _ _ _ D.toCore.toCore
  exact W.orthogonalProjectionOnto.toLinearMap

theorem submoduleProjection_inner
    (D : MetricFiberData V) (W : Submodule Real V) (v : V) (w : W) :
    D.inner (submoduleProjection D W v : V) w = D.inner v w  := by sorry

@[simp]
theorem submoduleProjection_eq_self
    (D : MetricFiberData V) (W : Submodule Real V) (v : V) (hv : v ∈ W) :
    submoduleProjection D W v = ⟨v, hv⟩  := by sorry

theorem submoduleProjection_inner_self_le
    (D : MetricFiberData V) (W : Submodule Real V) (v : V) :
    D.inner (submoduleProjection D W v : V) (submoduleProjection D W v : V) ≤
      D.inner v v  := by sorry

theorem exists_metric_linearEquiv
    (DV : MetricFiberData V) (DW : MetricFiberData W)
    (hfin : Module.finrank ℝ V = Module.finrank ℝ W) :
    ∃ e : V ≃ₗ[ℝ] W, ∀ v w, DW.inner (e v) (e w) = DV.inner v w  := by sorry

section MetricEquiv

variable {V' W' : Type*}
  [NormedAddCommGroup V'] [NormedSpace Real V'] [FiniteDimensional Real V']
  [NormedAddCommGroup W'] [NormedSpace Real W'] [FiniteDimensional Real W']

theorem exists_metric_cle
    (DV : MetricFiberData V') (DW : MetricFiberData W')
    (hfin : Module.finrank Real V' = Module.finrank Real W') :
    ∃ e : V' ≃L[Real] W',
      ∀ v w, DW.inner (e v) (e w) = DV.inner v w  := by sorry

end MetricEquiv

def adjoint (DV : MetricFiberData V) (DW : MetricFiberData W)
    (A : V →ₗ[Real] W) : W →ₗ[Real] V :=
  DV.flat.symm.toLinearMap.comp
    (A.dualMap.comp DW.flat.toLinearMap)

theorem adjoint_inner
    (DV : MetricFiberData V) (DW : MetricFiberData W)
    (A : V →ₗ[Real] W) (y : W) (x : V) :
    DV.inner (adjoint DV DW A y) x = DW.inner y (A x)  := by sorry

section InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

def ofInnerProductSpace : MetricFiberData F :=
  ofFlat
    { toFun := fun v => (innerSL ℝ v).toLinearMap
      map_add' := by
        intro v w
        ext z
        exact inner_add_left v w z
      map_smul' := by
        intro c v
        ext z
        exact real_inner_smul_left v z c }
    (by
      intro v w h
      apply ext_inner_right ℝ
      intro z
      exact congrArg (fun f : Module.Dual ℝ F => f z) h)
    (fun v w => (real_inner_comm v w).symm)
    (fun v => real_inner_self_nonneg)

@[simp] theorem ofInnerProductSpace_inner (v w : F) :
    (ofInnerProductSpace (F := F)).inner v w = Inner.inner ℝ v w  := by sorry

end InnerProductSpace

end MetricFiberData

end

end DifferentialGeometry.Tensor0SBundle

