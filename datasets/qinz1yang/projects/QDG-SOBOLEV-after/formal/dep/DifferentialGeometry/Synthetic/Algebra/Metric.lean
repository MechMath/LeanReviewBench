import dep.DifferentialGeometry.Synthetic.Algebra.TensorAlgebra
import dep.DifferentialGeometry.Synthetic.Analysis.NablaOnTensors
import dep.DifferentialGeometry.Synthetic.Analysis.TimeOnTensors



set_option autoImplicit false
set_option linter.unusedSectionVars false
open BigOperators
open SyntheticTensor





section FlatHelper
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]


def flat_covector (g : TensorData R V 0 2) (Y : V) : V →ₗ[R] R where
  toFun Z := g ![Y, Z] ![]
  map_add' a b := by
    have h := g.map_update_add ![Y, a] 1 a b
    have hu : ∀ v, Function.update (![Y, a] : Fin 2 → V) 1 v = ![Y, v] := by
      intro v; ext i; fin_cases i <;> simp [Function.update]
    simp only [hu] at h; exact congr_arg (· ![]) h
  map_smul' c a := by
    have h := congr_arg (· ![]) (g.map_update_smul ![Y, a] 1 c a)
    simp only [MultilinearMap.smul_apply, smul_eq_mul] at h
    rwa [show Function.update (![Y, a] : Fin 2 → V) 1 (c • a) = ![Y, c • a] from by
          ext i; fin_cases i <;> simp [Function.update],
         show Function.update (![Y, a] : Fin 2 → V) 1 a = ![Y, a] from by
          ext i; fin_cases i <;> simp [Function.update]] at h

@[simp] theorem flat_covector_apply (g : TensorData R V 0 2) (Y Z : V) :
    flat_covector g Y Z = g ![Y, Z] ![]  := by sorry

end FlatHelper






structure MetricDuality (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] where
  g_tensor : TensorData R V 0 2
  symm_tensor : swap_covariant 0 1 g_tensor = g_tensor
  g_inv : TensorData R V 2 0
  eq_of_forall_g_eq : ∀ X Y : V,
    (∀ Z : V, g_tensor ![X, Z] ![] = g_tensor ![Y, Z] ![]) → X = Y
  
  inverse_eval : ∀ (Y : V) (α : V →ₗ[R] R),
    g_inv ![] ![α, flat_covector g_tensor Y] = α Y
  
  sharp_spec : ∀ (α : V →ₗ[R] R), ∃ v : V, ∀ Z : V, g_tensor ![v, Z] ![] = α Z





section MetricDefs
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

def MetricDuality.g (met : MetricDuality R V) (X Y : V) : R :=
  met.g_tensor ![X, Y] ![]


def MetricDuality.flat (met : MetricDuality R V) (X : V) : V →ₗ[R] R :=
  flat_covector met.g_tensor X

@[simp] theorem MetricDuality.flat_apply (met : MetricDuality R V) (X Y : V) :
    met.flat X Y = met.g X Y  := by sorry

theorem MetricDuality.inverse_eval' (met : MetricDuality R V)
    (Y : V) (α : V →ₗ[R] R) :
    met.g_inv ![] ![α, met.flat Y] = α Y  := by sorry

theorem MetricDuality.g_symm (met : MetricDuality R V) (X Y : V) :
    met.g X Y = met.g Y X  := by sorry

theorem MetricDuality.g_add_left (met : MetricDuality R V) (X Y Z : V) :
    met.g (X + Y) Z = met.g X Z + met.g Y Z  := by sorry

theorem MetricDuality.g_smul_left (met : MetricDuality R V) (c : R) (X Z : V) :
    met.g (c • X) Z = c * met.g X Z  := by sorry

theorem MetricDuality.g_add_right (met : MetricDuality R V) (X Y Z : V) :
    met.g X (Y + Z) = met.g X Y + met.g X Z  := by sorry

theorem MetricDuality.g_smul_right (met : MetricDuality R V) (c : R) (X Z : V) :
    met.g X (c • Z) = c * met.g X Z  := by sorry

def SharpSpec (met : MetricDuality R V) : Prop :=
  ∀ (α : V →ₗ[R] R), ∃ v : V, ∀ Z : V, met.g v Z = α Z


theorem MetricDuality.sharpSpec (met : MetricDuality R V) : SharpSpec met  := by sorry

noncomputable def MetricDuality.sharp (met : MetricDuality R V) (α : V →ₗ[R] R) : V :=
  open Classical in
  if h : ∃ v : V, ∀ Z : V, met.g v Z = α Z then h.choose else (0 : V)

theorem MetricDuality.g_sharp (met : MetricDuality R V)
    (α : V →ₗ[R] R) (Z : V) :
    met.g (met.sharp α) Z = α Z  := by sorry

theorem MetricDuality.sharp_flat (met : MetricDuality R V)
    (Y : V) :
    met.sharp (met.flat Y) = Y  := by sorry

theorem MetricDuality.flat_injective (met : MetricDuality R V) :
    Function.Injective met.flat  := by sorry

theorem MetricDuality.sharp_add (met : MetricDuality R V)
    (α β : V →ₗ[R] R) :
    met.sharp (α + β) = met.sharp α + met.sharp β  := by sorry

theorem MetricDuality.sharp_smul (met : MetricDuality R V)
    (c : R) (α : V →ₗ[R] R) :
    met.sharp (c • α) = c • met.sharp α  := by sorry

end MetricDefs





section MetricCompat
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

def IsMetricCompatible
    (emb : DerivationEmbedding k R V) (conn : V → V → V) (met : MetricDuality R V) : Prop :=
  ∀ X Y Z : V,
    (emb.embed X) (met.g Y Z) = met.g (conn X Y) Z + met.g Y (conn X Z)


private theorem g_tensor_of (met : MetricDuality R V) (f : Fin 2 → V) :
    met.g_tensor f ![] = met.g (f 0) (f 1)  := by sorry

theorem nabla_g_zero
    (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met) (X : V) :
    nabla_tensor emb conn ha hl X met.g_tensor = 0  := by sorry

end MetricCompat





section NablaDualFlat
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

theorem nabla_dual_flat
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met) (X Y : V) :
    nabla_dual emb conn ha hl X (met.flat Y) = met.flat (conn X Y)  := by sorry

end NablaDualFlat





section NablaGInv
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

theorem nabla_g_inv_zero
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met)
    (X : V) :
    nabla_tensor emb conn ha hl X met.g_inv = 0  := by sorry

end NablaGInv





section NablaContractDef
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]


def NablaTensorContractComm
    (emb : DerivationEmbedding k R V) (atr : AbstractTrace R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y) : Prop :=
  ∀ (X : V) {r s : ℕ} (T : TensorData R V (r + 1) (s + 1)),
    nabla_tensor emb conn ha hl X (atr.tensor_contract T) =
    atr.tensor_contract (nabla_tensor emb conn ha hl X T)

end NablaContractDef





section IndexOps
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

noncomputable def lower_index (met : MetricDuality R V) (atr : AbstractTrace R V)
    {r s : ℕ} (idx : Fin (r + 1)) (T : TensorData R V (r + 1) s) : TensorData R V r (s + 1) :=
  contract_general atr idx ⟨1, by omega⟩
    ((show 0 + (r + 1) = r + 1 from by omega) ▸
     (show 2 + s = s + 1 + 1 from by omega) ▸
     tensor_prod (r₁ := 0) (s₁ := 2) (r₂ := r + 1) (s₂ := s) met.g_tensor T)

noncomputable def raise_index (met : MetricDuality R V) (atr : AbstractTrace R V)
    {r s : ℕ} (idx : Fin (s + 1)) (T : TensorData R V r (s + 1)) : TensorData R V (r + 1) s :=
  contract_general atr ⟨1, by omega⟩ idx
    ((show 2 + r = r + 1 + 1 from by omega) ▸
     (show 0 + (s + 1) = s + 1 from by omega) ▸
     tensor_prod (r₁ := 2) (s₁ := 0) (r₂ := r) (s₂ := s + 1) met.g_inv T)

noncomputable def metric_trace (met : MetricDuality R V) (atr : AbstractTrace R V)
    {r s : ℕ} (idx₁ : Fin (s + 2)) (idx₂ : Fin (s + 1))
    (T : TensorData R V r (s + 2)) : TensorData R V r s :=
  contract_general atr (0 : Fin (r + 1)) idx₂ (raise_index met atr idx₁ T)

end IndexOps





section LowerIndexEval
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]


theorem lower_index_eval_11 (met : MetricDuality R V) (atr : AbstractTrace R V)
    (T : TensorData R V 1 1) (X Y : V) :
    lower_index met atr (0 : Fin 1) T ![X, Y] ![] = T ![Y] ![met.flat X]  := by sorry

end LowerIndexEval





section NablaMetricTrace
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]


private theorem td_congr {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {r s : ℕ} {T₁ T₂ : TensorData R V r s} (h : T₁ = T₂) (vs αs) :
    T₁ vs αs = T₂ vs αs  := by sorry

theorem nabla_raise_index_comm
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met)
    (atr : AbstractTrace R V)
    (h_ntc : NablaTensorContractComm emb atr conn ha hl)
    (Y : V) {r s : ℕ} (idx : Fin (s + 1)) (T : TensorData R V r (s + 1)) :
    nabla_tensor emb conn ha hl Y (raise_index met atr idx T) =
    raise_index met atr idx (nabla_tensor emb conn ha hl Y T)  := by sorry

theorem nabla_metric_trace_comm
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V)
    (h_ntc : NablaTensorContractComm emb atr conn ha hl)
    (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met)
    (X : V) {r s : ℕ} (idx₁ : Fin (s + 2)) (idx₂ : Fin (s + 1))
    (T : TensorData R V r (s + 2)) :
    nabla_tensor emb conn ha hl X (metric_trace met atr idx₁ idx₂ T) =
    metric_trace met atr idx₁ idx₂ (nabla_tensor emb conn ha hl X T)  := by sorry

end NablaMetricTrace





section TimeDeriv
variable {R V : Type*} {A Time : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [CommRing A] [Algebra R A]

theorem t_const_V (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (t : Time) (X : V) :
    dt_tensor td t (fun _ => vectorToData (R := R) X)
      (fun vs αs => td.isSmoothFam_const (vectorToData (R := R) X vs αs)) = 0  := by sorry

theorem t_const_scalar (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (t : Time) (c : R) :
    dt_tensor td t (fun _ => scalarToData (R := R) (V := V) c)
      (fun vs αs => td.isSmoothFam_const
        (scalarToData (R := R) (V := V) c vs αs)) = 0  := by sorry

theorem dt_metric_const_args
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (met_fam : Time → MetricDuality R V)
    (h_met : ∀ vs αs, td.isSmoothFam (fun τ => (met_fam τ).g_tensor vs αs))
    (X Y : V) (t : Time) :
    td.dt_apply (fun s => (met_fam s).g X Y) t =
    dt_tensor td t (fun s => (met_fam s).g_tensor) h_met ![X, Y] ![]  := by sorry

theorem t_metric_one_varying_left
    (td : TimeDerivativeData R A Time)
    (met : MetricDuality R V) (f : Time → V) (Y : V) (t : Time) :
    td.dt_apply (fun s => met.g (f s) Y) t =
    td.dt_apply (fun s => met.flat Y (f s)) t  := by sorry

theorem t_metric_one_varying_right
    (td : TimeDerivativeData R A Time)
    (met : MetricDuality R V) (X : V) (f : Time → V) (t : Time) :
    td.dt_apply (fun s => met.g X (f s)) t =
    td.dt_apply (fun s => met.flat X (f s)) t  := by sorry

theorem t_metric_partial_variations
    (td : TimeDerivativeData R A Time)
    (met_fam : Time → MetricDuality R V) (X Y : V) (t : Time) :
    td.dt_apply (fun s => (met_fam s).g X Y) t =
    td.dt_apply (fun s => (met_fam s).g_tensor ![X, Y] ![]) t  := by sorry

theorem t_metric_fixed_both_varying
    (td : TimeDerivativeData R A Time)
    (met : MetricDuality R V) (f_X f_Y : Time → V) (t : Time) :
    td.dt_apply (fun s => met.g (f_X s) (f_Y s)) t =
    td.dt_apply (fun s => met.flat (f_X s) (f_Y s)) t  := by sorry

end TimeDeriv
