import dep.DifferentialGeometry.Geometry.Metric.MetricFiberData.Defs
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace DifferentialGeometry.Tensor0SBundle

noncomputable section

open scoped BigOperators

namespace MetricFiberData

variable {V W : Type*}

def realFlatLinear : Real →ₗ[Real] Module.Dual Real Real where
  toFun := fun a =>
    { toFun := fun b => a * b
      map_add' := by
        intro b c
        ring
      map_smul' := by
        intro c b
        simp [smul_eq_mul, mul_left_comm] }
  map_add' := by
    intro a b
    ext
    simp
  map_smul' := by
    intro c a
    ext
    simp [smul_eq_mul]

def real : MetricFiberData Real :=
  MetricFiberData.ofFlat realFlatLinear
    (by
      intro a b h
      have h1 := congrArg (fun φ : Module.Dual Real Real => φ 1) h
      simpa [realFlatLinear] using h1)
    (by
      intro a b
      change a * b = b * a
      ring)
    (by
      intro a
      change 0 <= a * a
      nlinarith [sq_nonneg a])

def pullback [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (e : V ≃ₗ[Real] W) (D : MetricFiberData W) : MetricFiberData V where
  flat := e.trans (D.flat.trans e.dualMap)
  symm := by
    intro v w
    change D.flat (e v) (e w) = D.flat (e w) (e v)
    exact D.symm (e v) (e w)
  nonneg := by
    intro v
    change 0 <= D.flat (e v) (e v)
    exact D.nonneg (e v)

def ofFiniteDimensional (V : Type*) [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] : MetricFiberData V :=
  let e := (Module.finBasis ℝ V).equivFun.trans
    (WithLp.linearEquiv 2 ℝ (Fin (Module.finrank ℝ V) → ℝ)).symm
  pullback e ofInnerProductSpace

def homFlatLinear [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W) :
    (V →ₗ[Real] W) →ₗ[Real] Module.Dual Real (V →ₗ[Real] W) where
  toFun A :=
    { toFun := fun B =>
        LinearMap.trace Real V
          ((MetricFiberData.adjoint DV DW A).comp B)
      map_add' := by
        intro B C
        simp [LinearMap.comp_add, map_add]
      map_smul' := by
        intro c B
        simp [LinearMap.comp_smul, map_smul] }
  map_add' := by
    intro A B
    ext C
    have hdual :
        (A + B).dualMap = A.dualMap + B.dualMap := by
      ext φ x
      simp
    change
      LinearMap.trace Real V
          ((DV.flat.symm.toLinearMap.comp
            (((A + B).dualMap).comp DW.flat.toLinearMap)).comp C) =
        LinearMap.trace Real V
          ((DV.flat.symm.toLinearMap.comp
            (A.dualMap.comp DW.flat.toLinearMap)).comp C) +
          LinearMap.trace Real V
            ((DV.flat.symm.toLinearMap.comp
              (B.dualMap.comp DW.flat.toLinearMap)).comp C)
    rw [hdual]
    simp [LinearMap.add_comp, LinearMap.comp_add, map_add]
  map_smul' := by
    intro c A
    ext B
    have hdual :
        (c • A).dualMap = c • A.dualMap := by
      ext φ x
      simp
    change
      LinearMap.trace Real V
          ((DV.flat.symm.toLinearMap.comp
            (((c • A).dualMap).comp DW.flat.toLinearMap)).comp B) =
        c *
          LinearMap.trace Real V
            ((DV.flat.symm.toLinearMap.comp
              (A.dualMap.comp DW.flat.toLinearMap)).comp B)
    rw [hdual]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, map_smul]

theorem trace_adjoint_comp_eq_sum_inner
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    [NormedAddCommGroup W] [InnerProductSpace Real W] [FiniteDimensional Real W]
    (A B : V →ₗ[Real] W) :
    LinearMap.trace Real V ((LinearMap.adjoint A).comp B) =
      ∑ i : Fin (Module.finrank Real V),
        Inner.inner Real (A (stdOrthonormalBasis Real V i))
          (B (stdOrthonormalBasis Real V i))  := by sorry

theorem trace_adjoint_comp_nonneg
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    [NormedAddCommGroup W] [InnerProductSpace Real W] [FiniteDimensional Real W]
    (A : V →ₗ[Real] W) :
    0 <= LinearMap.trace Real V ((LinearMap.adjoint A).comp A)  := by sorry

theorem trace_adjoint_comp_eq_zero_iff
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    [NormedAddCommGroup W] [InnerProductSpace Real W] [FiniteDimensional Real W]
    (A : V →ₗ[Real] W) :
    LinearMap.trace Real V ((LinearMap.adjoint A).comp A) = 0 ↔ A = 0  := by sorry

theorem trace_adjoint_comp_comm
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    [NormedAddCommGroup W] [InnerProductSpace Real W] [FiniteDimensional Real W]
    (A B : V →ₗ[Real] W) :
    LinearMap.trace Real V ((LinearMap.adjoint A).comp B) =
      LinearMap.trace Real V ((LinearMap.adjoint B).comp A)  := by sorry

theorem metric_adjoint_eq_adjoint
    [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W) (A : V →ₗ[Real] W) :
    letI : InnerProductSpace.Core Real V := DV.toCore
    letI : NormedAddCommGroup V :=
      @InnerProductSpace.Core.toNormedAddCommGroup Real V _ _ _ DV.toCore
    letI : InnerProductSpace Real V :=
      @InnerProductSpace.ofCore Real V _ _ _ DV.toCore.toCore
    letI : InnerProductSpace.Core Real W := DW.toCore
    letI : NormedAddCommGroup W :=
      @InnerProductSpace.Core.toNormedAddCommGroup Real W _ _ _ DW.toCore
    letI : InnerProductSpace Real W :=
      @InnerProductSpace.ofCore Real W _ _ _ DW.toCore.toCore
    MetricFiberData.adjoint DV DW A = LinearMap.adjoint A  := by sorry

theorem homFlatLinear_comm [AddCommGroup V] [Module Real V]
    [FiniteDimensional Real V] [AddCommGroup W] [Module Real W]
    [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W)
    (A B : V →ₗ[Real] W) :
    homFlatLinear DV DW A B = homFlatLinear DV DW B A  := by sorry

theorem homFlatLinear_nonneg [AddCommGroup V] [Module Real V]
    [FiniteDimensional Real V] [AddCommGroup W] [Module Real W]
    [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W)
    (A : V →ₗ[Real] W) :
    0 <= homFlatLinear DV DW A A  := by sorry

theorem homFlatLinear_self_eq_zero_iff [AddCommGroup V] [Module Real V]
    [FiniteDimensional Real V] [AddCommGroup W] [Module Real W]
    [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W)
    (A : V →ₗ[Real] W) :
    homFlatLinear DV DW A A = 0 ↔ A = 0  := by sorry

private theorem hom_nonneg [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W) :
    Function.Injective (homFlatLinear DV DW) ∧
      (forall A B : V →ₗ[Real] W,
        homFlatLinear DV DW A B = homFlatLinear DV DW B A) ∧
      (forall A : V →ₗ[Real] W, 0 <= homFlatLinear DV DW A A)  := by sorry

def hom [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W) :
    MetricFiberData (V →ₗ[Real] W) :=
  MetricFiberData.ofFlat (homFlatLinear DV DW)
    (hom_nonneg DV DW).1
    (hom_nonneg DV DW).2.1
    (hom_nonneg DV DW).2.2

def homCLM [AddCommGroup V] [Module Real V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul Real V] [T2Space V]
    [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [ContinuousSMul Real W] [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W) :
    MetricFiberData (V →L[Real] W) :=
  MetricFiberData.pullback
    (LinearMap.toContinuousLinearMap (𝕜 := Real) (E := V) (F' := W)).symm
    (MetricFiberData.hom DV DW)

section Isometries

variable [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

@[simp] theorem pullback_inner (e : V ≃ₗ[ℝ] W) (D : MetricFiberData W) (v w : V) :
    (pullback e D).inner v w = D.inner (e v) (e w)  := by sorry

theorem hom_inner (DV : MetricFiberData V) (DW : MetricFiberData W)
    (A B : V →ₗ[ℝ] W) :
    (hom DV DW).inner A B = LinearMap.trace ℝ V ((adjoint DV DW A).comp B)  := by sorry

variable {V' W' : Type*}
  [AddCommGroup V'] [Module ℝ V'] [FiniteDimensional ℝ V']
  [AddCommGroup W'] [Module ℝ W'] [FiniteDimensional ℝ W']

theorem adjoint_congr
    (DV : MetricFiberData V) (DW : MetricFiberData W)
    (DV' : MetricFiberData V') (DW' : MetricFiberData W')
    (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W')
    (hV : ∀ v w, DV'.inner (eV v) (eV w) = DV.inner v w)
    (hW : ∀ v w, DW'.inner (eW v) (eW w) = DW.inner v w)
    (A : V →ₗ[ℝ] W) :
    adjoint DV' DW' (eW.toLinearMap.comp (A.comp eV.symm.toLinearMap)) =
      eV.toLinearMap.comp ((adjoint DV DW A).comp eW.symm.toLinearMap)  := by sorry

theorem hom_inner_congr
    (DV : MetricFiberData V) (DW : MetricFiberData W)
    (DV' : MetricFiberData V') (DW' : MetricFiberData W')
    (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W')
    (hV : ∀ v w, DV'.inner (eV v) (eV w) = DV.inner v w)
    (hW : ∀ v w, DW'.inner (eW v) (eW w) = DW.inner v w)
    (A B : V →ₗ[ℝ] W) :
    (hom DV' DW').inner
        (eW.toLinearMap.comp (A.comp eV.symm.toLinearMap))
        (eW.toLinearMap.comp (B.comp eV.symm.toLinearMap)) =
      (hom DV DW).inner A B  := by sorry

end Isometries

section InnerProductSpace

variable {F G : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

theorem adjoint_ofInnerProductSpace (A : F →ₗ[ℝ] G) :
    adjoint ofInnerProductSpace ofInnerProductSpace A = LinearMap.adjoint A  := by sorry

theorem hom_inner_eq_sum_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ F) (A B : F →ₗ[ℝ] G) :
    (hom ofInnerProductSpace ofInnerProductSpace).inner A B =
      ∑ i, Inner.inner ℝ (A (b i)) (B (b i))  := by sorry

end InnerProductSpace

end MetricFiberData

end

end DifferentialGeometry.Tensor0SBundle

