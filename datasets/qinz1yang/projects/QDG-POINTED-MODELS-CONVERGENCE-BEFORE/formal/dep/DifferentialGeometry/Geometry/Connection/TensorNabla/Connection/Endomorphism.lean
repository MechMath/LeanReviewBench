import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.Connection.Tangent
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.InducedConnection

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

private theorem contDiffWithinAt_clm_of_apply
    {D F : Type*} [NormedAddCommGroup D] [NormedSpace 𝕜 D]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {n : WithTop ℕ∞} {Γ : D → E →L[𝕜] F} {u : Set D} {y : D}
    (hΓ : ∀ v : E, ContDiffWithinAt 𝕜 n (fun z => Γ z v) u y) :
    ContDiffWithinAt 𝕜 n Γ u y  := by sorry

section ConnectionEndomorphism

variable [IsManifold I 2 M]

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
private theorem covariantDerivative_finset_sum
    {ι : Type*} (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (t : Finset ι) (σ : ι → (x : M) → TangentSpace I x)
    {x : M} (v : TangentSpace I x)
    (hσ : ∀ i, MDiffAt (T% (σ i)) x) :
    (cov (t.sum σ) x) v = t.sum (fun i => (cov (σ i) x) v)  := by sorry

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
omit [IsManifold I n M] in
lemma covariantDerivative_tangentConst_apply_contMDiffOn_baseSet
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov n)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (x₀ : M) (v : E) [IsManifold I (n + 1 + 1) M] :
    CMDiff[(trivializationAt E (TangentSpace I) x₀).baseSet] n
      (T% (fun p : M =>
        (cov (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ v) p) (X p)))  := by sorry

noncomputable def connectionEndomorphismInChartL
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x₀ : M) (y : E) : E →L[𝕜] E →L[𝕜] E := by
  classical
  let e := trivializationAt E (TangentSpace I) x₀
  let p := (extChartAt I x₀).symm y
  refine LinearMap.toContinuousLinearMap ?_
  refine
    { toFun := fun X =>
        LinearMap.toContinuousLinearMap
          { toFun := fun v =>
              if y ∈ (extChartAt I x₀).target then
                e.continuousLinearMapAt 𝕜 p
                  ((cov (tangentConstInChart x₀ v) p) (e.symmL 𝕜 p X))
              else
                0
            map_add' := ?_
            map_smul' := ?_ }
      map_add' := ?_
      map_smul' := ?_ }
  · intro v w
    by_cases hy : y ∈ (extChartAt I x₀).target
    · have hp_source : p ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hy
      have hp_base : p ∈ e.baseSet := by
        simpa [e, p, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp_source
      have hv : MDiffAt
          (T% (tangentConstInChart x₀ v : (p : M) → TangentSpace I p)) p :=
        mdifferentiableAt_tangentConstInChart_of_mem
          (x₀ := x₀) (p := p) v hp_base
      have hw : MDiffAt
          (T% (tangentConstInChart x₀ w : (p : M) → TangentSpace I p)) p :=
        mdifferentiableAt_tangentConstInChart_of_mem
          (x₀ := x₀) (p := p) w hp_base
      have hsection :
          (tangentConstInChart x₀ (v + w) : (p : M) → TangentSpace I p) =
            (tangentConstInChart x₀ v : (p : M) → TangentSpace I p) +
              tangentConstInChart x₀ w :=
        tangentConstInChart_add x₀ v w
      have hcov :
          cov ((tangentConstInChart x₀ v : (p : M) → TangentSpace I p) +
              tangentConstInChart x₀ w) p =
            cov (tangentConstInChart x₀ v) p +
              cov (tangentConstInChart x₀ w) p :=
        cov.isCovariantDerivativeOnUniv.add hv hw
      rw [ite_eq_left hy, ite_eq_left hy, ite_eq_left hy]
      rw [hsection, hcov]
      simp [map_add]
    · rw [ite_eq_right hy, ite_eq_right hy, ite_eq_right hy]
      simp
  · intro a v
    by_cases hy : y ∈ (extChartAt I x₀).target
    · have hp_source : p ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hy
      have hp_base : p ∈ e.baseSet := by
        simpa [e, p, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp_source
      have hv : MDiffAt
          (T% (tangentConstInChart x₀ v : (p : M) → TangentSpace I p)) p :=
        mdifferentiableAt_tangentConstInChart_of_mem
          (x₀ := x₀) (p := p) v hp_base
      have hsection :
          (tangentConstInChart x₀ (a • v) : (p : M) → TangentSpace I p) =
            a • (tangentConstInChart x₀ v : (p : M) → TangentSpace I p) :=
        tangentConstInChart_smul x₀ a v
      have hcov :
          cov (a • (tangentConstInChart x₀ v : (p : M) → TangentSpace I p)) p =
            a • cov (tangentConstInChart x₀ v) p :=
        cov.isCovariantDerivativeOnUniv.smul_const a hv
      rw [ite_eq_left hy, ite_eq_left hy]
      rw [hsection, hcov]
      simp [map_smul]
    · rw [ite_eq_right hy, ite_eq_right hy]
      simp
  · intro X Y
    ext v
    change (if y ∈ (extChartAt I x₀).target then
        e.continuousLinearMapAt 𝕜 p
          ((cov (tangentConstInChart x₀ v) p) (e.symmL 𝕜 p (X + Y)))
      else 0) =
      (if y ∈ (extChartAt I x₀).target then
        e.continuousLinearMapAt 𝕜 p
          ((cov (tangentConstInChart x₀ v) p) (e.symmL 𝕜 p X))
      else 0) +
      (if y ∈ (extChartAt I x₀).target then
        e.continuousLinearMapAt 𝕜 p
          ((cov (tangentConstInChart x₀ v) p) (e.symmL 𝕜 p Y))
      else 0)
    by_cases hy : y ∈ (extChartAt I x₀).target
    · rw [ite_eq_left hy, ite_eq_left hy, ite_eq_left hy]
      simp [map_add]
    · rw [ite_eq_right hy, ite_eq_right hy, ite_eq_right hy]
      simp
  · intro a X
    ext v
    change (if y ∈ (extChartAt I x₀).target then
        e.continuousLinearMapAt 𝕜 p
          ((cov (tangentConstInChart x₀ v) p) (e.symmL 𝕜 p (a • X)))
      else 0) =
      a •
        (if y ∈ (extChartAt I x₀).target then
          e.continuousLinearMapAt 𝕜 p
            ((cov (tangentConstInChart x₀ v) p) (e.symmL 𝕜 p X))
        else 0)
    by_cases hy : y ∈ (extChartAt I x₀).target
    · rw [ite_eq_left hy, ite_eq_left hy]
      simp [map_smul]
    · rw [ite_eq_right hy, ite_eq_right hy]
      simp

lemma connectionEndomorphismInChartL_apply_of_mem
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (X v : E) :
    connectionEndomorphismInChartL (𝕜 := 𝕜) (I := I) cov x₀ y X v =
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜
        ((extChartAt I x₀).symm y)
        ((cov (tangentConstInChart x₀ v)
          ((extChartAt I x₀).symm y))
          ((trivializationAt E (TangentSpace I) x₀).symmL 𝕜
            ((extChartAt I x₀).symm y) X))  := by sorry

lemma connectionEndomorphismInChartL_apply_of_notMem
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x₀ : M) {y : E}
    (hy : y ∉ (extChartAt I x₀).target) (X v : E) :
    connectionEndomorphismInChartL (𝕜 := 𝕜) (I := I) cov x₀ y X v = 0  := by sorry

lemma connectionEndomorphismInChartL_apply_modelVector
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : (x : M) → TangentSpace I x) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (v : E) :
    connectionEndomorphismInChartL (𝕜 := 𝕜) (I := I) cov x₀ y
        ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜
          ((extChartAt I x₀).symm y) (X ((extChartAt I x₀).symm y))) v =
      connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x₀ y v  := by sorry

lemma connectionEndomorphismInChartL_apply_center_modelVector
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : (x : M) → TangentSpace I x) (x : M) (v : E) :
    connectionEndomorphismInChartL (𝕜 := 𝕜) (I := I) cov x (extChartAt I x x)
        ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt 𝕜
          x (X x)) v =
      connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x
        (extChartAt I x x) v  := by sorry

lemma connectionEndomorphismInChartL_apply_center
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : (x : M) → TangentSpace I x) (x : M) (v : E) :
    connectionEndomorphismInChartL (𝕜 := 𝕜) (I := I) cov x (extChartAt I x x)
        (X x) v =
      connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x
        (extChartAt I x x) v  := by sorry

theorem covariantDerivative_modelInChart_center_eq_sum
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X V : (x : M) → TangentSpace I x) (x₀ : M)
    (hV : MDiffAt (T% V) x₀)
    (hz : ∀ i : Fin (Module.finrank 𝕜 E),
      MDiffAt
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
              (extChartAt I x₀ p))) x₀) :
    let b := Module.finBasis 𝕜 E
    let zfun : Fin (Module.finrank 𝕜 E) → M → 𝕜 :=
      fun i p =>
        b.coord i
          (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
            (extChartAt I x₀ p))
    tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀
        (fun p : M => (cov V p) (X p)) (extChartAt I x₀ x₀) =
      (∑ i : Fin (Module.finrank 𝕜 E),
        mvfderiv (I := I) (zfun i) x₀ (X x₀) • b i) +
        connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x₀
          (extChartAt I x₀ x₀)
          (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
            (extChartAt I x₀ x₀))  := by sorry

theorem covariantDerivative_modelInChart_eq_sum
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X V : (x : M) → TangentSpace I x) (x₀ p : M)
    (hp : p ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet)
    (hV : MDiffAt (T% V) p)
    (hz : ∀ i : Fin (Module.finrank 𝕜 E),
      MDiffAt
        (fun q : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
              (extChartAt I x₀ q))) p) :
    let b := Module.finBasis 𝕜 E
    let zfun : Fin (Module.finrank 𝕜 E) → M → 𝕜 :=
      fun i q =>
        b.coord i
          (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
            (extChartAt I x₀ q))
    tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀
        (fun q : M => (cov V q) (X q)) (extChartAt I x₀ p) =
      (∑ i : Fin (Module.finrank 𝕜 E),
        mvfderiv (I := I) (zfun i) p (X p) • b i) +
        connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x₀
          (extChartAt I x₀ p)
          (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
            (extChartAt I x₀ p))  := by sorry

omit [IsManifold I n M] in
lemma connectionEndomorphismInChart_apply_contDiffWithinAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov n)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (x₀ : M) (v : E) [IsManifold I (n + 1) M] [IsManifold I (n + 1 + 1) M] :
    ContDiffWithinAt 𝕜 n
      (fun y : E =>
        connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀ y v)
      (Set.range I) (extChartAt I x₀ x₀)  := by sorry

omit [IsManifold I n M] in
lemma connectionEndomorphismInChart_contDiffWithinAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov n)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (x₀ : M) [IsManifold I (n + 1) M] [IsManifold I (n + 1 + 1) M] :
    ContDiffWithinAt 𝕜 n
      (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
      (Set.range I) (extChartAt I x₀ x₀)  := by sorry

end ConnectionEndomorphism

end

end TensorLieDeriv
end DifferentialGeometry

