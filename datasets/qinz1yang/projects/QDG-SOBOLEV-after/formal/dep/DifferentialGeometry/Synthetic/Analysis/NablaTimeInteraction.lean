import dep.DifferentialGeometry.Synthetic.Analysis.NablaOnTensors
import dep.DifferentialGeometry.Synthetic.Analysis.TimeOnTensors



set_option autoImplicit false
set_option linter.unusedSectionVars false
open BigOperators
open SyntheticTensor





section FixedConn

variable {k R V : Type*} {A Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]


theorem t_nabla_tensor
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (h_st : SpatialTemporalComm emb td)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) {r s : ℕ} (T : Time → TensorData R V r s) (t : Time)
    (hT : ∀ vs αs, td.isSmoothFam (fun τ => T τ vs αs))
    (hXT : ∀ vs αs, td.isSmoothFam (fun τ => (emb.embed X) (T τ vs αs)))
    (hT_nabla : ∀ vs αs, td.isSmoothFam
      (fun τ => nabla_tensor emb conn ha hl X (T τ) vs αs)) :
    dt_tensor td t (fun τ => nabla_tensor emb conn ha hl X (T τ)) hT_nabla =
    nabla_tensor emb conn ha hl X (dt_tensor td t T hT)  := by sorry

end FixedConn





section ConnVar

variable {k R V : Type*} {A Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]


noncomputable def conn_var_tensor
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ τ, ∀ X Y Z, conn_fam τ X (Y + Z) = conn_fam τ X Y + conn_fam τ X Z)
    (hl_fam : ∀ τ, ∀ X (f : R) Y,
      conn_fam τ X (f • Y) = (emb.embed X) f • Y + f • conn_fam τ X Y)
    (t : Time) (X : V) {r s : ℕ} (T : TensorData R V r s)
    (h_nabla_smooth : ∀ vs αs, td.isSmoothFam
      (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T vs αs))
    : TensorData R V r s :=
  dt_tensor td t (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T)
    h_nabla_smooth


theorem conn_var_tensor_eval
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ τ, ∀ X Y Z, conn_fam τ X (Y + Z) = conn_fam τ X Y + conn_fam τ X Z)
    (hl_fam : ∀ τ, ∀ X (f : R) Y,
      conn_fam τ X (f • Y) = (emb.embed X) f • Y + f • conn_fam τ X Y)
    (t : Time) (X : V) {r s : ℕ} (T : TensorData R V r s)
    (h_nabla_smooth : ∀ vs αs, td.isSmoothFam
      (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T vs αs))
    (h_conn_smooth_v : ∀ i vs αs, td.isSmoothFam
      (fun τ => T (Function.update vs i (conn_fam τ X (vs i))) αs))
    (h_conn_smooth_c : ∀ j vs αs, td.isSmoothFam
      (fun τ => T vs (Function.update αs j
        (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))))
    (vs αs) :
    conn_var_tensor emb td conn_fam ha_fam hl_fam t X T h_nabla_smooth vs αs =
    - td.dt_apply (fun τ => ∑ i : Fin s,
        T (Function.update vs i (conn_fam τ X (vs i))) αs) t
    - td.dt_apply (fun τ => ∑ j : Fin r,
        T vs (Function.update αs j
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) t  := by sorry

end ConnVar





section VaryingConnT

variable {k R V : Type*} {A Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]


theorem t_nabla_eval
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (h_st : SpatialTemporalComm emb td)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ τ, ∀ X Y Z, conn_fam τ X (Y + Z) = conn_fam τ X Y + conn_fam τ X Z)
    (hl_fam : ∀ τ, ∀ X (f : R) Y,
      conn_fam τ X (f • Y) = (emb.embed X) f • Y + f • conn_fam τ X Y)
    (X : V) {r s : ℕ} (T : Time → TensorData R V r s) (t : Time)
    (hT : ∀ vs αs, td.isSmoothFam (fun τ => T τ vs αs))
    (hXT : ∀ vs αs, td.isSmoothFam (fun τ => (emb.embed X) (T τ vs αs)))
    (h_conn_smooth_v : ∀ i vs αs, td.isSmoothFam
      (fun τ => T τ (Function.update vs i (conn_fam τ X (vs i))) αs))
    (h_conn_smooth_c : ∀ j vs αs, td.isSmoothFam
      (fun τ => T τ vs (Function.update αs j
        (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))))
    (hT_nabla : ∀ vs αs, td.isSmoothFam
      (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (T τ) vs αs))
    (vs αs) :
    dt_tensor td t (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (T τ))
      hT_nabla vs αs =
    (emb.embed X) (td.dt_apply (fun τ => T τ vs αs) t)
    - td.dt_apply (fun τ => ∑ i : Fin s,
        T τ (Function.update vs i (conn_fam τ X (vs i))) αs) t
    - td.dt_apply (fun τ => ∑ j : Fin r,
        T τ vs (Function.update αs j
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) t  := by sorry

theorem conn_var_tensor_add
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ τ, ∀ X Y Z, conn_fam τ X (Y + Z) = conn_fam τ X Y + conn_fam τ X Z)
    (hl_fam : ∀ τ, ∀ X (f : R) Y,
      conn_fam τ X (f • Y) = (emb.embed X) f • Y + f • conn_fam τ X Y)
    (t : Time) (X : V) {r s : ℕ} (T₁ T₂ : TensorData R V r s)
    (h₁ : ∀ vs αs, td.isSmoothFam
      (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T₁ vs αs))
    (h₂ : ∀ vs αs, td.isSmoothFam
      (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T₂ vs αs))
    (h₁₂ : ∀ vs αs, td.isSmoothFam
      (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (T₁ + T₂) vs αs)) :
    conn_var_tensor emb td conn_fam ha_fam hl_fam t X (T₁ + T₂) h₁₂ =
    conn_var_tensor emb td conn_fam ha_fam hl_fam t X T₁ h₁ +
    conn_var_tensor emb td conn_fam ha_fam hl_fam t X T₂ h₂  := by sorry

theorem conn_var_tensor_smul
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ τ, ∀ X Y Z, conn_fam τ X (Y + Z) = conn_fam τ X Y + conn_fam τ X Z)
    (hl_fam : ∀ τ, ∀ X (f : R) Y,
      conn_fam τ X (f • Y) = (emb.embed X) f • Y + f • conn_fam τ X Y)
    (t : Time) (X : V) {r s : ℕ} (c : R) (T : TensorData R V r s)
    (hT_nabla : ∀ vs αs, td.isSmoothFam
      (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T vs αs))
    (h_cT_nabla : ∀ vs αs, td.isSmoothFam
      (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (c • T) vs αs)) :
    conn_var_tensor emb td conn_fam ha_fam hl_fam t X (c • T) h_cT_nabla =
    c • conn_var_tensor emb td conn_fam ha_fam hl_fam t X T hT_nabla  := by sorry

end VaryingConnT






section TLinearMap

variable {R V : Type*} {A Time : Type*}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [CommRing A] [Algebra R A]


theorem t_linear_map (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (t : Time)
    (ω : V →ₗ[R] R) (F : Time → V)
    (hVF : ∀ vs αs, td.isSmoothFam
      (fun τ => vectorToData (R := R) (F τ) vs αs)) :
    td.dt_apply (fun s => ω (F s)) t =
    dt_tensor td t (fun s => vectorToData (R := R) (F s)) hVF ![] ![ω]  := by sorry

end TLinearMap







section TConnApply

variable {k R V : Type*} {A Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]


theorem t_conn_apply
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (h_st : SpatialTemporalComm emb td)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) (F : Time → V) (t : Time)
    (hVF : ∀ vs αs, td.isSmoothFam
      (fun τ => vectorToData (R := R) (F τ) vs αs))
    (hXVF : ∀ vs αs, td.isSmoothFam
      (fun τ => (emb.embed X) (vectorToData (R := R) (F τ) vs αs)))
    (hVcF : ∀ vs αs, td.isSmoothFam
      (fun τ => vectorToData (R := R) (conn X (F τ)) vs αs))
    (hN_VF : ∀ vs αs, td.isSmoothFam
      (fun τ => nabla_tensor emb conn ha hl X (vectorToData (R := R) (F τ)) vs αs)) :
    dt_tensor td t (fun τ => vectorToData (R := R) (conn X (F τ))) hVcF =
    nabla_tensor emb conn ha hl X
      (dt_tensor td t (fun τ => vectorToData (R := R) (F τ)) hVF)  := by sorry

end TConnApply





section SlotLeibniz

variable {k R V : Type*} {A Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]


theorem TimeDerivativeData.dt_apply_leibniz_slot_vector
    (td : TimeDerivativeData R A Time) [TimeRegularFam td] [TimeRegularFam2 td]
    (conn_fam : Time → V → V → V)
    (X : V) {r s : ℕ} (T : Time → TensorData R V r s) (t : Time) (i : Fin s)
    (vs : Fin s → V) (αs : Fin r → V →ₗ[R] R)
    (h_2smooth : TimeRegularFam2.isSmoothFam2 (td := td)
      (fun p : Time × Time =>
        T p.1 (Function.update vs i (conn_fam p.2 X (vs i))) αs)) :
    td.dt_apply
        (fun τ => T τ (Function.update vs i (conn_fam τ X (vs i))) αs) t
      = td.dt_apply
          (fun τ => T t (Function.update vs i (conn_fam τ X (vs i))) αs) t
        + td.dt_apply
            (fun τ => T τ (Function.update vs i (conn_fam t X (vs i))) αs) t  := by sorry

theorem TimeDerivativeData.dt_apply_leibniz_slot_covector
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td] [TimeRegularFam2 td]
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ τ, ∀ X Y Z, conn_fam τ X (Y + Z) = conn_fam τ X Y + conn_fam τ X Z)
    (hl_fam : ∀ τ, ∀ X (f : R) Y,
      conn_fam τ X (f • Y) = (emb.embed X) f • Y + f • conn_fam τ X Y)
    (X : V) {r s : ℕ} (T : Time → TensorData R V r s) (t : Time) (j : Fin r)
    (vs : Fin s → V) (αs : Fin r → V →ₗ[R] R)
    (h_2smooth : TimeRegularFam2.isSmoothFam2 (td := td)
      (fun p : Time × Time =>
        T p.1 vs (Function.update αs j
          (nabla_dual emb (conn_fam p.2) (ha_fam p.2) (hl_fam p.2) X (αs j))))) :
    td.dt_apply
        (fun τ => T τ vs (Function.update αs j
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) t
      = td.dt_apply
          (fun τ => T t vs (Function.update αs j
            (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) t
        + td.dt_apply
            (fun τ => T τ vs (Function.update αs j
              (nabla_dual emb (conn_fam t) (ha_fam t) (hl_fam t) X (αs j)))) t  := by sorry

end SlotLeibniz
