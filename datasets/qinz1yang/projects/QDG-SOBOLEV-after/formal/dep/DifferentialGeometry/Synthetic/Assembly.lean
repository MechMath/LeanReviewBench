import dep.DifferentialGeometry.Synthetic.Algebra.VectorFieldAlgebra
import dep.DifferentialGeometry.Synthetic.Algebra.TensorAlgebra
import dep.DifferentialGeometry.Synthetic.Algebra.Metric
import dep.DifferentialGeometry.Synthetic.Geometry.Connection
import dep.DifferentialGeometry.Synthetic.Analysis.NablaTimeInteraction
import dep.DifferentialGeometry.Synthetic.Operator.Variation
import dep.DifferentialGeometry.Synthetic.Flow.RicciFlow.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

open SyntheticTensor

structure SyntheticManifoldData (k R V : Type*)
    [Field k] [CommRing R] [Algebra k R]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V] where
  
  emb : DerivationEmbedding k R V
  
  atr : AbstractTrace R V
  
  conn : V → V → V
  
  conn_add_right : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z
  
  conn_add_left : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z
  
  conn_smul_left : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z
  
  conn_leibniz : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y
  
  nabla_tr_comm : NablaTrComm emb atr conn conn_add_right conn_leibniz
  
  nabla_contract_comm : NablaTensorContractComm emb atr conn conn_add_right conn_leibniz

structure RiemannianManifoldData (k R V : Type*)
    [Field k] [CommRing R] [Algebra k R] [Invertible (2 : R)]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
    extends SyntheticManifoldData k R V where
  
  met : MetricDuality R V
  
  metric_compat : IsMetricCompatible emb conn met
  
  torsion_free : IsTorsionFree emb conn

structure TimeEvolvingManifoldData (k R V Time A : Type*)
    [Field k] [CommRing R] [Algebra k R] [Invertible (2 : R)]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
    [CommRing A] [Algebra R A]
    extends RiemannianManifoldData k R V where
  
  td : TimeDerivativeData R A Time
  
  [td_regular : TimeRegularFam td]
  
  spatial_temporal_comm : SpatialTemporalComm emb td
  
  time_tr_comm : TimeTrComm atr td

attribute [instance] TimeEvolvingManifoldData.td_regular


structure ScalarTimeEvolvingManifoldData (k R V Time A : Type*)
    [Field k] [CommRing R] [Algebra k R] [Invertible (2 : R)]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
    [CommRing A] [Algebra R A]
    extends RiemannianManifoldData k R V where
  
  td : TimeDerivativeData R A Time
  
  [td_regular : TimeRegularFam td]
  
  spatial_temporal_comm : SpatialTemporalComm emb td
  
  u_fam : Time → R
  
  h_u : td.isSmoothFam u_fam

attribute [instance] ScalarTimeEvolvingManifoldData.td_regular


structure TimeEvolvingFamilyManifoldData (k R V Time A : Type*)
    [Field k] [CommRing R] [Algebra k R] [Invertible (2 : R)]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
    [CommRing A] [Algebra R A] where
  
  emb : DerivationEmbedding k R V
  
  atr : AbstractTrace R V
  
  td : TimeDerivativeData R A Time
  
  [td_regular : TimeRegularFam td]
  
  g_fam : Time → MetricDuality R V
  
  h_met : ∀ vs αs, td.isSmoothFam (fun τ => (g_fam τ).g_tensor vs αs)
  
  conn_fam : Time → V → V → V
  
  ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z
  
  hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z
  
  hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z
  
  hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y
  
  spatial_temporal_comm : SpatialTemporalComm emb td
  
  time_tr_comm : TimeTrComm atr td
  
  nabla_tr_comm : ∀ s, NablaTrComm emb atr (conn_fam s) (ha_fam s) (hl_fam s)
  
  nabla_contract_comm : ∀ s, NablaTensorContractComm emb atr (conn_fam s) (ha_fam s) (hl_fam s)
  
  levi_civita : ∀ s, IsLeviCivita emb (conn_fam s) (g_fam s)

attribute [instance] TimeEvolvingFamilyManifoldData.td_regular


structure RicciFlowBundle (k R V Time A : Type*)
    [Field k] [CommRing R] [Algebra k R] [Invertible (2 : R)]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
    [CommRing A] [Algebra R A]
    extends TimeEvolvingFamilyManifoldData k R V Time A where
  
  [td_regular2 : TimeRegularFam2 td]
  
  ricci_flow : IsRicciFlow emb td atr g_fam h_met conn_fam ha_fam hal_fam hsl_fam hl_fam
  
  nabla_time_product_rule : NablaTimeProductRule emb td conn_fam ha_fam hl_fam

attribute [instance] RicciFlowBundle.td_regular2
