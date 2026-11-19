import dep.DifferentialGeometry.Synthetic.Algebra.VectorFieldAlgebra
import dep.DifferentialGeometry.Synthetic.Algebra.TensorAlgebra
import dep.DifferentialGeometry.Synthetic.Algebra.Metric
import dep.DifferentialGeometry.Synthetic.Geometry.Connection
import dep.DifferentialGeometry.Synthetic.Geometry.ConnectionExtended
import dep.DifferentialGeometry.Synthetic.Analysis.TimeOnTensors
import dep.DifferentialGeometry.Synthetic.Operator.Variation

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false



open SyntheticTensor





section RmTensor

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]


noncomputable def Rm_tensor
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    : TensorData R V 1 3 where
  toFun vs :=
    { toFun := fun αs => (αs 0) (Rm emb conn (vs 0) (vs 1) (vs 2))
      map_update_add' := by
        intro inst αs idx α₁ α₂
        have : inst = instDecidableEqFin 1 := Subsingleton.elim _ _; subst this
        have hidx : idx = (0 : Fin 1) := Subsingleton.elim _ _; subst hidx
        simp [Function.update, LinearMap.add_apply]
      map_update_smul' := by
        intro inst αs idx c α
        have : inst = instDecidableEqFin 1 := Subsingleton.elim _ _; subst this
        have hidx : idx = (0 : Fin 1) := Subsingleton.elim _ _; subst hidx
        simp [Function.update, LinearMap.smul_apply, smul_eq_mul] }
  map_update_add' := by
    intro inst vs idx v₁ v₂; ext αs
    have : inst = instDecidableEqFin 3 := Subsingleton.elim _ _; subst this
    simp only [MultilinearMap.coe_mk, MultilinearMap.add_apply]
    fin_cases idx
    · 
      change (αs 0) (Rm emb conn (Function.update vs 0 (v₁ + v₂) 0) (Function.update vs 0 (v₁ + v₂) 1) (Function.update vs 0 (v₁ + v₂) 2)) =
           (αs 0) (Rm emb conn (Function.update vs 0 v₁ 0) (Function.update vs 0 v₁ 1) (Function.update vs 0 v₁ 2)) +
           (αs 0) (Rm emb conn (Function.update vs 0 v₂ 0) (Function.update vs 0 v₂ 1) (Function.update vs 0 v₂ 2))
      simp only [Fin.isValue, Function.update_self, ne_eq, one_ne_zero, not_false_eq_true, Function.update_of_ne, Fin.reduceEq]
      rw [Rm_add_X emb conn ha hal, map_add]
    · 
      change (αs 0) (Rm emb conn (Function.update vs 1 (v₁ + v₂) 0) (Function.update vs 1 (v₁ + v₂) 1) (Function.update vs 1 (v₁ + v₂) 2)) =
           (αs 0) (Rm emb conn (Function.update vs 1 v₁ 0) (Function.update vs 1 v₁ 1) (Function.update vs 1 v₁ 2)) +
           (αs 0) (Rm emb conn (Function.update vs 1 v₂ 0) (Function.update vs 1 v₂ 1) (Function.update vs 1 v₂ 2))
      simp only [Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true, Function.update_of_ne, Function.update_self, Fin.reduceEq]
      rw [Rm_add_Y emb conn ha hal, map_add]
    · 
      change (αs 0) (Rm emb conn (Function.update vs 2 (v₁ + v₂) 0) (Function.update vs 2 (v₁ + v₂) 1) (Function.update vs 2 (v₁ + v₂) 2)) =
           (αs 0) (Rm emb conn (Function.update vs 2 v₁ 0) (Function.update vs 2 v₁ 1) (Function.update vs 2 v₁ 2)) +
           (αs 0) (Rm emb conn (Function.update vs 2 v₂ 0) (Function.update vs 2 v₂ 1) (Function.update vs 2 v₂ 2))
      simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Function.update_self]
      rw [Rm_add_Z emb conn ha hal, map_add]
  map_update_smul' := by
    intro inst vs idx c v; ext αs
    have : inst = instDecidableEqFin 3 := Subsingleton.elim _ _; subst this
    simp only [MultilinearMap.coe_mk, MultilinearMap.smul_apply, smul_eq_mul]
    fin_cases idx
    · change (αs 0) (Rm emb conn (Function.update vs 0 (c • v) 0) (Function.update vs 0 (c • v) 1) (Function.update vs 0 (c • v) 2)) =
           c * (αs 0) (Rm emb conn (Function.update vs 0 v 0) (Function.update vs 0 v 1) (Function.update vs 0 v 2))
      simp only [Fin.isValue, Function.update_self, ne_eq, one_ne_zero, not_false_eq_true, Function.update_of_ne, Fin.reduceEq]
      rw [Rm_smul_X emb conn hal hsl hl, map_smul, smul_eq_mul]
    · change (αs 0) (Rm emb conn (Function.update vs 1 (c • v) 0) (Function.update vs 1 (c • v) 1) (Function.update vs 1 (c • v) 2)) =
           c * (αs 0) (Rm emb conn (Function.update vs 1 v 0) (Function.update vs 1 v 1) (Function.update vs 1 v 2))
      simp only [Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true, Function.update_of_ne, Function.update_self, Fin.reduceEq]
      rw [Rm_smul_Y emb conn hal hsl hl, map_smul, smul_eq_mul]
    · change (αs 0) (Rm emb conn (Function.update vs 2 (c • v) 0) (Function.update vs 2 (c • v) 1) (Function.update vs 2 (c • v) 2)) =
           c * (αs 0) (Rm emb conn (Function.update vs 2 v 0) (Function.update vs 2 v 1) (Function.update vs 2 v 2))
      simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Function.update_self]
      rw [Rm_smul_Z emb conn ha hsl hl, map_smul, smul_eq_mul]


theorem Rm_tensor_eval
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X Y Z : V) (ω : V →ₗ[R] R) :
    Rm_tensor emb conn ha hal hsl hl ![X, Y, Z] ![ω] = ω (Rm emb conn X Y Z)  := by sorry

end RmTensor





section RicciFormTensor

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]


noncomputable def ricciForm_tensor
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) : TensorData R V 0 2 where
  toFun vs := MultilinearMap.constOfIsEmpty _ _
    (Rc emb conn ha hal hsl hl atr (vs 0) (vs 1))
  map_update_add' := by
    intro inst vs idx v₁ v₂; ext αs
    have : inst = instDecidableEqFin 2 := Subsingleton.elim _ _; subst this
    simp only [MultilinearMap.constOfIsEmpty, MultilinearMap.add_apply, MultilinearMap.coe_mk]
    fin_cases idx
    · 
      simp only [Fin.zero_eta, Fin.isValue, Function.update_self, ne_eq, one_ne_zero, not_false_eq_true, Function.update_of_ne, Function.const_apply]
      change Rc emb conn ha hal hsl hl atr (v₁ + v₂) (vs 1) =
           Rc emb conn ha hal hsl hl atr v₁ (vs 1) + Rc emb conn ha hal hsl hl atr v₂ (vs 1)
      unfold Rc
      rw [show RcEndo emb conn ha hal hsl hl (v₁ + v₂) (vs 1) =
          RcEndo emb conn ha hal hsl hl v₁ (vs 1) + RcEndo emb conn ha hal hsl hl v₂ (vs 1) from
        LinearMap.ext (fun Y => Rm_add_Y emb conn ha hal Y v₁ v₂ (vs 1))]
      exact map_add atr.tr _ _
    · 
      simp only [Fin.mk_one, Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true, Function.update_of_ne, Function.update_self, Function.const_apply]
      change Rc emb conn ha hal hsl hl atr (vs 0) (v₁ + v₂) =
           Rc emb conn ha hal hsl hl atr (vs 0) v₁ + Rc emb conn ha hal hsl hl atr (vs 0) v₂
      exact (RcCovector emb conn ha hal hsl hl atr (vs 0)).map_add v₁ v₂
  map_update_smul' := by
    intro inst vs idx c v; ext αs
    have : inst = instDecidableEqFin 2 := Subsingleton.elim _ _; subst this
    simp only [MultilinearMap.constOfIsEmpty, MultilinearMap.smul_apply, MultilinearMap.coe_mk, smul_eq_mul]
    fin_cases idx
    · simp only [Function.update]
      change Rc emb conn ha hal hsl hl atr (c • v) (vs 1) =
           c * Rc emb conn ha hal hsl hl atr v (vs 1)
      unfold Rc
      rw [show RcEndo emb conn ha hal hsl hl (c • v) (vs 1) =
          c • RcEndo emb conn ha hal hsl hl v (vs 1) from
        LinearMap.ext (fun Y => Rm_smul_Y emb conn hal hsl hl c Y v (vs 1))]
      rw [atr.tr.map_smul, smul_eq_mul]
    · simp only [Function.update]
      change Rc emb conn ha hal hsl hl atr (vs 0) (c • v) =
           c * Rc emb conn ha hal hsl hl atr (vs 0) v
      have := (RcCovector emb conn ha hal hsl hl atr (vs 0)).map_smul c v
      rwa [smul_eq_mul] at this


theorem ricciForm_tensor_eval
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (X Z : V) :
    ricciForm_tensor emb conn ha hal hsl hl atr ![X, Z] ![] =
    Rc emb conn ha hal hsl hl atr X Z  := by sorry

theorem ricciForm_tensor_smul_eval
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (c : R) (X Z : V) :
    (c • ricciForm_tensor emb conn ha hal hsl hl atr) ![X, Z] ![] =
    c * Rc emb conn ha hal hsl hl atr X Z  := by sorry

end RicciFormTensor





section RicciFlowDef

variable {k R V Time : Type*} {A : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]


def IsRicciFlow
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (g_fam : Time → MetricDuality R V)
    (h_met : ∀ vs αs, td.isSmoothFam (fun τ => (g_fam τ).g_tensor vs αs))
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    : Prop :=
  ∀ t, metric_var_form td g_fam h_met t =
    (-2 : R) • ricciForm_tensor emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr


theorem IsRicciFlow.evolution
    {emb : DerivationEmbedding k R V}
    {td : TimeDerivativeData R A Time} [TimeRegularFam td]
    {atr : AbstractTrace R V}
    {g_fam : Time → MetricDuality R V}
    {h_met : ∀ vs αs, td.isSmoothFam (fun τ => (g_fam τ).g_tensor vs αs)}
    {conn_fam : Time → V → V → V}
    {ha_fam hal_fam hsl_fam hl_fam}
    (h : IsRicciFlow emb td atr g_fam h_met conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (t : Time) : metric_var_form td g_fam h_met t =
    (-2 : R) • ricciForm_tensor emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr  := by sorry

end RicciFlowDef





section ProductRule





set_option linter.unusedVariables false

variable {k R V Time : Type*} {A : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]


private theorem nablaTimeProductRule_hT_nabla_of_aux
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td] [TimeRegularFam2 td]
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ τ, ∀ X Y Z, conn_fam τ X (Y + Z) = conn_fam τ X Y + conn_fam τ X Z)
    (hl_fam : ∀ τ, ∀ X (f : R) Y,
      conn_fam τ X (f • Y) = (emb.embed X) f • Y + f • conn_fam τ X Y)
    (X : V) {r s : ℕ} (T : Time → TensorData R V r s)
    (hXT : ∀ vs αs, td.isSmoothFam (fun τ => (emb.embed X) (T τ vs αs)))
    (h_2smooth_v : ∀ (i : Fin s) vs αs,
      TimeRegularFam2.isSmoothFam2 (td := td)
        (fun p : Time × Time =>
          T p.1 (Function.update vs i (conn_fam p.2 X (vs i))) αs))
    (h_2smooth_c : ∀ (j : Fin r) vs αs,
      TimeRegularFam2.isSmoothFam2 (td := td)
        (fun p : Time × Time =>
          T p.1 vs (Function.update αs j
            (nabla_dual emb (conn_fam p.2) (ha_fam p.2) (hl_fam p.2) X (αs j))))) :
    ∀ vs αs, td.isSmoothFam
      (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (T τ) vs αs)  := by sorry

private theorem nablaTimeProductRule_h_nabla_t_of_aux
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td] [TimeRegularFam2 td]
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ τ, ∀ X Y Z, conn_fam τ X (Y + Z) = conn_fam τ X Y + conn_fam τ X Z)
    (hl_fam : ∀ τ, ∀ X (f : R) Y,
      conn_fam τ X (f • Y) = (emb.embed X) f • Y + f • conn_fam τ X Y)
    (X : V) {r s : ℕ} (T : Time → TensorData R V r s) (t : Time)
    (h_2smooth_v : ∀ (i : Fin s) vs αs,
      TimeRegularFam2.isSmoothFam2 (td := td)
        (fun p : Time × Time =>
          T p.1 (Function.update vs i (conn_fam p.2 X (vs i))) αs))
    (h_2smooth_c : ∀ (j : Fin r) vs αs,
      TimeRegularFam2.isSmoothFam2 (td := td)
        (fun p : Time × Time =>
          T p.1 vs (Function.update αs j
            (nabla_dual emb (conn_fam p.2) (ha_fam p.2) (hl_fam p.2) X (αs j))))) :
    ∀ vs αs, td.isSmoothFam
      (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (T t) vs αs)  := by sorry

def NablaTimeProductRule
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td] [TimeRegularFam2 td]
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ τ, ∀ X Y Z, conn_fam τ X (Y + Z) = conn_fam τ X Y + conn_fam τ X Z)
    (hl_fam : ∀ τ, ∀ X (f : R) Y, conn_fam τ X (f • Y) = (emb.embed X) f • Y + f • conn_fam τ X Y)
    : Prop :=
  ∀ (X : V) {r s : ℕ} (T : Time → TensorData R V r s) (t : Time)
    (hT : ∀ vs αs, td.isSmoothFam (fun τ => T τ vs αs))
    (hXT : ∀ vs αs, td.isSmoothFam (fun τ => (emb.embed X) (T τ vs αs)))
    (h_2smooth_v : ∀ (i : Fin s) vs αs,
      TimeRegularFam2.isSmoothFam2 (td := td)
        (fun p : Time × Time =>
          T p.1 (Function.update vs i (conn_fam p.2 X (vs i))) αs))
    (h_2smooth_c : ∀ (j : Fin r) vs αs,
      TimeRegularFam2.isSmoothFam2 (td := td)
        (fun p : Time × Time =>
          T p.1 vs (Function.update αs j
            (nabla_dual emb (conn_fam p.2) (ha_fam p.2) (hl_fam p.2) X (αs j))))),
    dt_tensor td t (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (T τ))
      (nablaTimeProductRule_hT_nabla_of_aux emb td conn_fam ha_fam hl_fam X T
        hXT h_2smooth_v h_2smooth_c) =
    conn_var_tensor emb td conn_fam ha_fam hl_fam t X (T t)
      (nablaTimeProductRule_h_nabla_t_of_aux emb td conn_fam ha_fam hl_fam X T t
        h_2smooth_v h_2smooth_c) +
    nabla_tensor emb (conn_fam t) (ha_fam t) (hl_fam t) X (dt_tensor td t T hT)

end ProductRule
