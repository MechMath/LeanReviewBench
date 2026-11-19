import dep.DifferentialGeometry.Synthetic.Algebra.VectorFieldAlgebra
import dep.DifferentialGeometry.Synthetic.Algebra.Metric
import Mathlib.Tactic.Abel



set_option autoImplicit false
set_option linter.unusedSectionVars false
open SyntheticTensor






theorem char_ne_2_of_invertible_two {R : Type*} [MonoidWithZero R]
    [OfNat R 2] [Invertible (2 : R)] (a : R) (h : (2 : R) * a = 0) : a = 0  := by sorry

section Conditions
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

def IsTorsionFree (emb : DerivationEmbedding k R V) (conn : V → V → V) : Prop :=
  ∀ X Y : V, conn X Y - conn Y X = bracket emb X Y

def IsLeviCivita (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (met : MetricDuality R V) : Prop :=
  IsMetricCompatible emb conn met ∧ IsTorsionFree emb conn

end Conditions





section ConnHelpers
variable {V : Type*} [AddCommGroup V]

theorem conn_zero_left (conn : V → V → V)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z) (Z : V) :
    conn 0 Z = 0  := by sorry

theorem conn_neg_left (conn : V → V → V)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z) (X Z : V) :
    conn (-X) Z = -conn X Z  := by sorry

theorem conn_sub_left (conn : V → V → V)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z) (A B Z : V) :
    conn (A - B) Z = conn A Z - conn B Z  := by sorry

theorem conn_zero_right (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z) (X : V) :
    conn X 0 = 0  := by sorry

theorem conn_neg_right (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z) (X Y : V) :
    conn X (-Y) = -conn X Y  := by sorry

theorem conn_sub_right (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z) (X A B : V) :
    conn X (A - B) = conn X A - conn X B  := by sorry

end ConnHelpers





section Curvature
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

noncomputable def Rm (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (X Y Z : V) : V :=
  conn X (conn Y Z) - conn Y (conn X Z) - conn (bracket emb X Y) Z

theorem Rm_antisymm (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (X Y Z : V) :
    Rm emb conn X Y Z = -Rm emb conn Y X Z  := by sorry

theorem Rm_add_Z (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (_hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (X Y Z₁ Z₂ : V) :
    Rm emb conn X Y (Z₁ + Z₂) = Rm emb conn X Y Z₁ + Rm emb conn X Y Z₂  := by sorry

theorem Rm_add_X (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (X₁ X₂ Y Z : V) :
    Rm emb conn (X₁ + X₂) Y Z = Rm emb conn X₁ Y Z + Rm emb conn X₂ Y Z  := by sorry

theorem Rm_add_Y (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (X Y₁ Y₂ Z : V) :
    Rm emb conn X (Y₁ + Y₂) Z = Rm emb conn X Y₁ Z + Rm emb conn X Y₂ Z  := by sorry

theorem Rm_smul_Z (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (_hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (f : R) (X Y Z : V) :
    Rm emb conn X Y (f • Z) = f • Rm emb conn X Y Z  := by sorry

theorem Rm_smul_Y (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (f : R) (X Y Z : V) :
    Rm emb conn X (f • Y) Z = f • Rm emb conn X Y Z  := by sorry

theorem Rm_smul_X (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (f : R) (X Y Z : V) :
    Rm emb conn (f • X) Y Z = f • Rm emb conn X Y Z  := by sorry

end Curvature





section Bianchi
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

theorem first_bianchi (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (_hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (h_tf : IsTorsionFree emb conn)
    (X Y Z : V) :
    Rm emb conn X Y Z + Rm emb conn Y Z X + Rm emb conn Z X Y = 0  := by sorry

end Bianchi





section Koszul
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]


private theorem g_sub_left' (met : MetricDuality R V) (A B C : V) :
    met.g (A - B) C = met.g A C - met.g B C  := by sorry

private theorem g_sub_right' (met : MetricDuality R V) (A B C : V) :
    met.g A (B - C) = met.g A B - met.g A C  := by sorry

theorem levi_civita_uniqueness
    (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (_ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (_hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (_hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met)
    (h_tf : IsTorsionFree emb conn) (X Y Z : V) :
    2 * met.g (conn X Y) Z =
      (emb.embed X) (met.g Y Z) + (emb.embed Y) (met.g Z X) - (emb.embed Z) (met.g X Y)
      - met.g X (bracket emb Y Z) + met.g Y (bracket emb Z X) + met.g Z (bracket emb X Y)  := by sorry

end Koszul





section RmMetric
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]


theorem Rm_metric_antisymm
    (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met)
    (X Y Z W : V) :
    met.g (Rm emb conn X Y Z) W = -met.g (Rm emb conn X Y W) Z  := by sorry

end RmMetric





section SecondBianchi
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]


noncomputable def covDerivRm (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (X Y Z W : V) : V :=
  conn X (Rm emb conn Y Z W) - Rm emb conn (conn X Y) Z W
  - Rm emb conn Y (conn X Z) W - Rm emb conn Y Z (conn X W)

theorem second_bianchi
    (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (h_tf : IsTorsionFree emb conn)
    (X Y Z W : V) :
    covDerivRm emb conn X Y Z W + covDerivRm emb conn Y Z X W +
    covDerivRm emb conn Z X Y W = 0  := by sorry

end SecondBianchi





section RicciIdentity
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

def secondCovDerivCommutator (conn : V → V → V) (X Y Z : V) : V :=
  conn X (conn Y Z) - conn Y (conn X Z) - conn (conn X Y - conn Y X) Z

theorem ricci_identity
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (_hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (h_tf : IsTorsionFree emb conn) (X Y Z : V) :
    secondCovDerivCommutator conn X Y Z = Rm emb conn X Y Z  := by sorry

end RicciIdentity





section RicciTensor
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

noncomputable def RcEndo (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X Z : V) : V →ₗ[R] V where
  toFun Y := Rm emb conn Y X Z
  map_add' Y₁ Y₂ := Rm_add_X emb conn ha hal Y₁ Y₂ X Z
  map_smul' f Y := by
    simp only [RingHom.id_apply]; exact Rm_smul_X emb conn hal hsl hl f Y X Z

noncomputable def Rc (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (X Z : V) : R :=
  atr.tr (RcEndo emb conn ha hal hsl hl X Z)

end RicciTensor
