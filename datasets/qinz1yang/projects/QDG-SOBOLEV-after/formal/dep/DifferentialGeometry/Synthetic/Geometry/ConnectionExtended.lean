import dep.DifferentialGeometry.Synthetic.Geometry.Connection
import dep.DifferentialGeometry.Synthetic.Analysis.NablaOnTensors
import Mathlib.Tactic.LinearCombination



set_option autoImplicit false
set_option linter.unusedSectionVars false
open SyntheticTensor





section MetricHelpers
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem MetricDuality.g_neg_left (met : MetricDuality R V) (X Y : V) :
    met.g (-X) Y = -met.g X Y  := by sorry

theorem MetricDuality.g_neg_right (met : MetricDuality R V) (X Y : V) :
    met.g X (-Y) = -met.g X Y  := by sorry

theorem MetricDuality.g_sub_left (met : MetricDuality R V) (A B C : V) :
    met.g (A - B) C = met.g A C - met.g B C  := by sorry

theorem MetricDuality.g_sub_right (met : MetricDuality R V) (A B C : V) :
    met.g A (B - C) = met.g A B - met.g A C  := by sorry

end MetricHelpers





section RmSymmBlocks
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

private theorem metric_bianchi
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (met : MetricDuality R V)
    (h_tf : IsTorsionFree emb conn) (A B C D : V) :
    met.g (Rm emb conn A B C) D + met.g (Rm emb conn B C A) D +
    met.g (Rm emb conn C A B) D = 0  := by sorry

theorem Rm_symm_blocks
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met)
    (h_tf : IsTorsionFree emb conn)
    [Invertible (2 : R)]
    (X Y Z W : V) :
    met.g (Rm emb conn X Y Z) W = met.g (Rm emb conn Z W X) Y  := by sorry

end RmSymmBlocks





section RXY
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]


noncomputable def R_XY (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X Y : V) {r s : ℕ} (T : TensorData R V r s) : TensorData R V r s :=
  nabla_tensor emb conn ha hl X (nabla_tensor emb conn ha hl Y T)
  - nabla_tensor emb conn ha hl Y (nabla_tensor emb conn ha hl X T)
  - nabla_tensor emb conn ha hl (bracket emb X Y) T


theorem R_XY_eval (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X Y : V) {r s : ℕ} (T : TensorData R V r s) (vs αs) :
    R_XY emb conn ha hl X Y T vs αs =
    nabla_tensor emb conn ha hl X (nabla_tensor emb conn ha hl Y T) vs αs -
    nabla_tensor emb conn ha hl Y (nabla_tensor emb conn ha hl X T) vs αs -
    nabla_tensor emb conn ha hl (bracket emb X Y) T vs αs  := by sorry

theorem R_XY_scalar (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X Y : V) (f : R) :
    R_XY emb conn ha hl X Y (scalarToData f) ![] ![] = 0  := by sorry

theorem R_XY_vector (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X Y U : V) :
    R_XY emb conn ha hl X Y (vectorToData (R := R) U) =
    vectorToData (R := R) (Rm emb conn X Y U)  := by sorry

end RXY





section TensorRicci02
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]


theorem nabla_02_eval
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) (T : TensorData R V 0 2) (U W : V) :
    nabla_tensor emb conn ha hl X T ![U, W] ![] =
    (emb.embed X) (T ![U, W] ![]) - T ![conn X U, W] ![] - T ![U, conn X W] ![]  := by sorry

theorem tensor_ricci_identity_02
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (h_tf : IsTorsionFree emb conn)
    (X Y U W : V) (T : TensorData R V 0 2) :
    R_XY emb conn ha hl X Y T ![U, W] ![] =
    -T ![Rm emb conn X Y U, W] ![] - T ![U, Rm emb conn X Y W] ![]  := by sorry

end TensorRicci02





section ScalarRicci
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]


noncomputable def RcCovector
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (X : V) : V →ₗ[R] R where
  toFun Z := Rc emb conn ha hal hsl hl atr X Z
  map_add' Z₁ Z₂ := by
    simp only [Rc]
    rw [show RcEndo emb conn ha hal hsl hl X (Z₁ + Z₂) =
        RcEndo emb conn ha hal hsl hl X Z₁ + RcEndo emb conn ha hal hsl hl X Z₂ from
      LinearMap.ext (fun Y => Rm_add_Z emb conn ha hal Y X Z₁ Z₂)]
    exact map_add atr.tr _ _
  map_smul' f Z := by
    simp only [Rc, RingHom.id_apply, smul_eq_mul]
    rw [show RcEndo emb conn ha hal hsl hl X (f • Z) =
        f • RcEndo emb conn ha hal hsl hl X Z from
      LinearMap.ext (fun Y => Rm_smul_Z emb conn ha hsl hl f Y X Z)]
    exact atr.tr.map_smul f _


noncomputable def RicciEndomorphism
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) : V →ₗ[R] V where
  toFun X := met.sharp (RcCovector emb conn ha hal hsl hl atr X)
  map_add' X₁ X₂ := by
    have h : RcCovector emb conn ha hal hsl hl atr (X₁ + X₂) =
        RcCovector emb conn ha hal hsl hl atr X₁ +
        RcCovector emb conn ha hal hsl hl atr X₂ := by
      apply LinearMap.ext; intro Z
      simp only [RcCovector, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, Rc]
      rw [show RcEndo emb conn ha hal hsl hl (X₁ + X₂) Z =
          RcEndo emb conn ha hal hsl hl X₁ Z + RcEndo emb conn ha hal hsl hl X₂ Z from
        LinearMap.ext (fun Y => Rm_add_Y emb conn ha hal Y X₁ X₂ Z)]
      exact map_add atr.tr _ _
    rw [h, met.sharp_add]
  map_smul' f X := by
    have h : RcCovector emb conn ha hal hsl hl atr (f • X) =
        f • RcCovector emb conn ha hal hsl hl atr X := by
      apply LinearMap.ext; intro Z
      simp only [RcCovector, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
        smul_eq_mul, Rc]
      rw [show RcEndo emb conn ha hal hsl hl (f • X) Z =
          f • RcEndo emb conn ha hal hsl hl X Z from
        LinearMap.ext (fun Y => Rm_smul_Y emb conn hal hsl hl f Y X Z)]
      exact atr.tr.map_smul f _
    simp only [RingHom.id_apply]; rw [h, met.sharp_smul]


theorem RicciEndomorphism_spec
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (X Z : V) :
    met.g (RicciEndomorphism emb conn ha hal hsl hl atr met X) Z =
    Rc emb conn ha hal hsl hl atr X Z  := by sorry

noncomputable def ScalarCurvature
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) : R :=
  atr.tr (RicciEndomorphism emb conn ha hal hsl hl atr met)

end ScalarRicci





section CovDerivDefs
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]


noncomputable def covDerivRc
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (Y Z X : V) : R :=
  (emb.embed Y) (Rc emb conn ha hal hsl hl atr Z X) -
  Rc emb conn ha hal hsl hl atr (conn Y Z) X -
  Rc emb conn ha hal hsl hl atr Z (conn Y X)


noncomputable def grad_R
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (X : V) : R :=
  (emb.embed X) (ScalarCurvature emb conn ha hal hsl hl atr met)

end CovDerivDefs





section KoszulConnection
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]


noncomputable def koszul_rhs (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V) (X Y Z : V) : R :=
  (emb.embed X) (met.g Y Z) + (emb.embed Y) (met.g Z X) - (emb.embed Z) (met.g X Y)
  - met.g X (bracket emb Y Z) + met.g Y (bracket emb Z X) + met.g Z (bracket emb X Y)


private theorem koszul_compat_key (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V) (A B C : V) :
    koszul_rhs emb met A B C + koszul_rhs emb met A C B =
    2 * (emb.embed A) (met.g B C)  := by sorry

private theorem koszul_torsion_key (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V) (A B C : V) :
    koszul_rhs emb met A B C - koszul_rhs emb met B A C =
    2 * met.g C (bracket emb A B)  := by sorry

noncomputable def koszul_covector (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V) (X Y : V) : V →ₗ[R] R where
  toFun Z := koszul_rhs emb met X Y Z
  map_add' := fun Z₁ Z₂ => by
    simp only [koszul_rhs]
    rw [show (emb.embed (Z₁ + Z₂)) (met.g X Y) =
        (emb.embed Z₁) (met.g X Y) + (emb.embed Z₂) (met.g X Y) from by
      rw [map_add, Derivation.add_apply]]
    rw [met.g_add_right Y Z₁ Z₂, (emb.embed X).map_add,
        met.g_add_left Z₁ Z₂ X, (emb.embed Y).map_add,
        bracket_add_right emb Y Z₁ Z₂, met.g_add_right X,
        bracket_add_left emb Z₁ Z₂ X, met.g_add_right Y,
        met.g_add_left Z₁ Z₂]
    ring
  map_smul' := fun c Z => by
    simp only [koszul_rhs, RingHom.id_apply, smul_eq_mul]
    
    rw [show (emb.embed (c • Z)) (met.g X Y) = c * (emb.embed Z) (met.g X Y) from by
      rw [map_smul, Derivation.smul_apply, smul_eq_mul]]
    
    rw [met.g_smul_right c Y Z, met.g_smul_left c Z X]
    
    rw [show (emb.embed X) (c * met.g Y Z) =
        c * (emb.embed X) (met.g Y Z) + met.g Y Z * (emb.embed X) c from by
      have := (emb.embed X).leibniz c (met.g Y Z); simp only [smul_eq_mul] at this; exact this]
    rw [show (emb.embed Y) (c * met.g Z X) =
        c * (emb.embed Y) (met.g Z X) + met.g Z X * (emb.embed Y) c from by
      have := (emb.embed Y).leibniz c (met.g Z X); simp only [smul_eq_mul] at this; exact this]
    
    rw [bracket_smul_right emb c Y Z, bracket_smul_left emb c Z X,
        show action emb X c = (emb.embed X) c from rfl,
        show action emb Y c = (emb.embed Y) c from rfl,
        met.g_smul_left c Z (bracket emb X Y)]
    
    simp only [MetricDuality.g_add_right, MetricDuality.g_sub_right,
               MetricDuality.g_smul_right]
    rw [met.g_symm Z X]; ring


noncomputable def koszul_connection (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V)
    [Invertible (2 : R)] (X Y : V) : V :=
  met.sharp (⅟(2 : R) • koszul_covector emb met X Y)


theorem koszul_connection_spec (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V)
    [Invertible (2 : R)] (X Y Z : V) :
    2 * met.g (koszul_connection emb met X Y) Z =
    koszul_rhs emb met X Y Z  := by sorry

theorem koszul_torsion_free (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V)
    [Invertible (2 : R)] :
    IsTorsionFree emb (koszul_connection emb met)  := by sorry

theorem koszul_metric_compat (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V)
    [Invertible (2 : R)] :
    IsMetricCompatible emb (koszul_connection emb met) met  := by sorry

theorem levi_civita_exists (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V)
    [Invertible (2 : R)] :
    IsLeviCivita emb (koszul_connection emb met) met  := by sorry

theorem levi_civita_unique (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V)
    [Invertible (2 : R)]
    (h_mc : IsMetricCompatible emb conn met)
    (h_tf : IsTorsionFree emb conn) (X Y : V) :
    conn X Y = koszul_connection emb met X Y  := by sorry

theorem koszul_connection_add_right (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V) [Invertible (2 : R)]
    (X Y₁ Y₂ : V) :
    koszul_connection emb met X (Y₁ + Y₂) =
    koszul_connection emb met X Y₁ + koszul_connection emb met X Y₂  := by sorry

theorem koszul_connection_add_left (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V) [Invertible (2 : R)]
    (X₁ X₂ Z : V) :
    koszul_connection emb met (X₁ + X₂) Z =
    koszul_connection emb met X₁ Z + koszul_connection emb met X₂ Z  := by sorry

theorem koszul_connection_smul_left (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V) [Invertible (2 : R)]
    (f : R) (X Z : V) :
    koszul_connection emb met (f • X) Z =
    f • koszul_connection emb met X Z  := by sorry

theorem koszul_connection_leibniz (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V) [Invertible (2 : R)]
    (X : V) (f : R) (Y : V) :
    koszul_connection emb met X (f • Y) =
    (emb.embed X) f • Y + f • koszul_connection emb met X Y  := by sorry

end KoszulConnection





section ContractedBianchi
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]


theorem covDerivRm_sum_endo
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (h_tf : IsTorsionFree emb conn) (X Y Z W : V) :
    covDerivRm emb conn X Y Z W + covDerivRm emb conn Y Z X W +
    covDerivRm emb conn Z X Y W = 0  := by sorry

end ContractedBianchi
