import dep.DifferentialGeometry.Synthetic.Algebra.Metric
import dep.DifferentialGeometry.Synthetic.Analysis.TimeOnTensors
import dep.DifferentialGeometry.Synthetic.Analysis.NablaTimeInteraction
import dep.DifferentialGeometry.Synthetic.Geometry.Connection
import dep.DifferentialGeometry.Synthetic.Geometry.ConnectionExtended
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false



open SyntheticTensor





section MetricZero
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

lemma metric_zero_right (met : MetricDuality R V) (X : V) : met.g X 0 = 0  := by sorry

lemma metric_zero_left (met : MetricDuality R V) (X : V) : met.g 0 X = 0  := by sorry

end MetricZero





section MetricVariation

variable {R V : Type*} {A : Type*} {Time : Type*}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [CommRing A] [Algebra R A]


noncomputable def metric_var_form
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (g_fam : Time → MetricDuality R V)
    (h_met : ∀ vs αs, td.isSmoothFam (fun τ => (g_fam τ).g_tensor vs αs))
    (t : Time) : TensorData R V 0 2 :=
  dt_tensor td t (fun s => (g_fam s).g_tensor) h_met

lemma metric_var_form_eval
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (g_fam : Time → MetricDuality R V)
    (h_met : ∀ vs αs, td.isSmoothFam (fun τ => (g_fam τ).g_tensor vs αs))
    (t : Time) (X Y : V) :
    metric_var_form td g_fam h_met t ![X, Y] ![] =
    td.dt_apply (fun s => (g_fam s).g X Y) t  := by sorry

lemma metric_var_form_symm
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (g_fam : Time → MetricDuality R V)
    (h_met : ∀ vs αs, td.isSmoothFam (fun τ => (g_fam τ).g_tensor vs αs))
    (t : Time) (A' B : V) :
    metric_var_form td g_fam h_met t ![A', B] ![] =
    metric_var_form td g_fam h_met t ![B, A'] ![]  := by sorry

end MetricVariation





section CovDerivH

variable {k R V : Type*} {A : Type*} {Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]


noncomputable def h_cov_deriv
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (g_fam : Time → MetricDuality R V)
    (h_met : ∀ vs αs, td.isSmoothFam (fun τ => (g_fam τ).g_tensor vs αs))
    (conn : V → V → V)
    (t : Time) (X Y Z : V) : R :=
  action emb X (metric_var_form td g_fam h_met t ![Y, Z] ![])
  - metric_var_form td g_fam h_met t ![conn X Y, Z] ![]
  - metric_var_form td g_fam h_met t ![Y, conn X Z] ![]

end CovDerivH





section Palatini

variable {k R V : Type*} {A : Type*} {Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]


private lemma mvf_sub_right
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (g_fam : Time → MetricDuality R V)
    (h_met : ∀ vs αs, td.isSmoothFam (fun τ => (g_fam τ).g_tensor vs αs))
    (t : Time) (A' B C : V) :
    metric_var_form td g_fam h_met t ![A', B - C] ![] =
    metric_var_form td g_fam h_met t ![A', B] ![] -
      metric_var_form td g_fam h_met t ![A', C] ![]  := by sorry

theorem connection_variation
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (h_st : SpatialTemporalComm emb td)
    (g_fam : Time → MetricDuality R V)
    (h_met : ∀ vs αs, td.isSmoothFam (fun τ => (g_fam τ).g_tensor vs αs))
    (h_emb_met : ∀ (W U U' : V),
      td.isSmoothFam (fun s => (emb.embed W) ((g_fam s).g U U')))
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z : V, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z : V, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_mc : ∀ s, IsMetricCompatible emb (conn_fam s) (g_fam s))
    (h_tf : ∀ s, IsTorsionFree emb (conn_fam s))
    (X Y Z : V) (t : Time)
    (h_conn_smooth : td.isSmoothFam (fun s => (g_fam s).g (conn_fam s X Y) Z)) :
    2 * td.dt_apply (fun s => (g_fam s).g (conn_fam s X Y) Z) t =
    h_cov_deriv emb td g_fam h_met (conn_fam t) t X Y Z +
    h_cov_deriv emb td g_fam h_met (conn_fam t) t Y X Z -
    h_cov_deriv emb td g_fam h_met (conn_fam t) t Z X Y +
    2 * metric_var_form td g_fam h_met t ![conn_fam t X Y, Z] ![]  := by sorry

end Palatini





section NablaFam

variable {k R V Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]


noncomputable abbrev nabla_fam
    (emb : DerivationEmbedding k R V)
    (g_fam : Time → MetricDuality R V)
    [Invertible (2 : R)] (t : Time) : V → V → V :=
  koszul_connection emb (g_fam t)

end NablaFam





section RaiseVariation

variable {R V : Type*} {A : Type*} {Time : Type*}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [CommRing A] [Algebra R A]


theorem raise_variation_const
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (g_fam : Time → MetricDuality R V)
    (T : TensorData R V 0 2) (X Y : V) (t : Time) :
    td.dt_apply (fun s => (g_fam s).g ((g_fam s).sharp (flat_covector T X)) Y) t = 0  := by sorry

theorem raise_variation
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (g_fam : Time → MetricDuality R V)
    (h_met : ∀ vs αs, td.isSmoothFam (fun τ => (g_fam τ).g_tensor vs αs))
    (T : TensorData R V 0 2) (X Y : V) (t : Time)
    (h_decomp : td.dt_apply (fun s => (g_fam s).g ((g_fam s).sharp (flat_covector T X)) Y) t =
      metric_var_form td g_fam h_met t ![((g_fam t).sharp (flat_covector T X)), Y] ![] +
      td.dt_apply (fun s => (g_fam t).flat Y ((g_fam s).sharp (flat_covector T X))) t) :
    td.dt_apply (fun s => (g_fam t).flat Y ((g_fam s).sharp (flat_covector T X))) t =
    - metric_var_form td g_fam h_met t ![((g_fam t).sharp (flat_covector T X)), Y] ![]  := by sorry

end RaiseVariation





section TrGVariation

variable {R V : Type*} {A : Type*} {Time : Type*}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [CommRing A] [Algebra R A]


theorem tr_g_variation
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (g_fam : Time → MetricDuality R V)
    (atr : AbstractTrace R V)
    (T : TensorData R V 0 2)
    (idx₁ : Fin 2) (idx₂ : Fin 1)
    (t : Time)
    (h_smooth : ∀ vs αs, td.isSmoothFam
      (fun τ => metric_trace (g_fam τ) atr idx₁ idx₂ T vs αs)) :
    td.dt_apply (fun s =>
      (metric_trace (g_fam s) atr idx₁ idx₂ T) ![] ![]) t =
    dt_tensor td t (fun s =>
      metric_trace (g_fam s) atr idx₁ idx₂ T) h_smooth ![] ![]  := by sorry

end TrGVariation
