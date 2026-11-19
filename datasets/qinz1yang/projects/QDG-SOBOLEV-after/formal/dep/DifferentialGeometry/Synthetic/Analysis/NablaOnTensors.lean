import dep.DifferentialGeometry.Synthetic.Algebra.TensorAlgebra
import Mathlib.Algebra.BigOperators.Group.Finset.Basic



set_option autoImplicit false
set_option linter.unusedSectionVars false
open BigOperators
open SyntheticTensor





section NablaDual

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]


def nabla_dual (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (conn_add : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (conn_leibniz : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) (α : V →ₗ[R] R) : V →ₗ[R] R where
  toFun Y := (emb.embed X) (α Y) - α (conn X Y)
  map_add' Y Z := by simp only [map_add, conn_add]; ring
  map_smul' c Y := by
    simp only [RingHom.id_apply, smul_eq_mul, map_smul α, smul_eq_mul]
    have h := (emb.embed X).leibniz c (α Y); simp only [smul_eq_mul] at h; rw [h]
    rw [conn_leibniz X c Y, map_add α, map_smul α, map_smul α]
    simp only [smul_eq_mul]; ring

theorem nabla_dual_map_add (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) (α₁ α₂ : V →ₗ[R] R) :
    nabla_dual emb conn ha hl X (α₁ + α₂) =
    nabla_dual emb conn ha hl X α₁ + nabla_dual emb conn ha hl X α₂  := by sorry

theorem nabla_dual_leibniz (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) (c : R) (α : V →ₗ[R] R) :
    nabla_dual emb conn ha hl X (c • α) =
    c • nabla_dual emb conn ha hl X α + (emb.embed X) c • α  := by sorry

end NablaDual





section FinsetHelper
variable {R : Type*} [CommRing R]

private lemma finset_sum_correction {n : ℕ} (idx : Fin n) (c extra : R)
    (f g : Fin n → R) (hne : ∀ j, j ≠ idx → f j = c * g j)
    (hk : f idx = extra + c * g idx) :
    ∑ j : Fin n, f j = extra + c * ∑ j : Fin n, g j  := by sorry

end FinsetHelper





section NablaTensor

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

private lemma embed_leibniz' (emb : DerivationEmbedding k R V) (X : V) (c f : R) :
    (emb.embed X) (c * f) = (emb.embed X) c * f + c * (emb.embed X) f  := by sorry

noncomputable def nabla_tensor (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) {r s : ℕ} (T : TensorData R V r s) : TensorData R V r s where
  toFun vs :=
    
    { toFun := fun αs =>
        (emb.embed X) (T vs αs)
        - ∑ i : Fin s, T (Function.update vs i (conn X (vs i))) αs
        - ∑ j : Fin r, T vs (Function.update αs j
            (nabla_dual emb conn ha hl X (αs j)))
      map_update_add' := by
        intro inst αs idx β₁ β₂
        have : inst = instDecidableEqFin r := Subsingleton.elim _ _; subst this
        have h1 := (T vs).map_update_add αs idx β₁ β₂
        rw [h1, map_add]
        have h2 : ∀ i, T (Function.update vs i (conn X (vs i)))
            (Function.update αs idx (β₁ + β₂)) =
            T (Function.update vs i (conn X (vs i))) (Function.update αs idx β₁) +
            T (Function.update vs i (conn X (vs i))) (Function.update αs idx β₂) :=
          fun i => (T (Function.update vs i (conn X (vs i)))).map_update_add αs idx β₁ β₂
        simp_rw [h2, Finset.sum_add_distrib]
        
        have h3 : ∀ j,
            T vs (Function.update (Function.update αs idx (β₁ + β₂)) j
              (nabla_dual emb conn ha hl X (Function.update αs idx (β₁ + β₂) j))) =
            T vs (Function.update (Function.update αs idx β₁) j
              (nabla_dual emb conn ha hl X (Function.update αs idx β₁ j))) +
            T vs (Function.update (Function.update αs idx β₂) j
              (nabla_dual emb conn ha hl X (Function.update αs idx β₂ j))) := by
          intro j; by_cases hj : j = idx
          · 
            subst hj
            simp only [Function.update_self, Function.update_idem]
            rw [nabla_dual_map_add]; exact (T vs).map_update_add αs j _ _
          · 
            rw [Function.update_of_ne hj, Function.update_of_ne hj, Function.update_of_ne hj,
                Function.update_comm (Ne.symm hj) _ _ αs,
                Function.update_comm (Ne.symm hj) _ _ αs,
                Function.update_comm (Ne.symm hj) _ _ αs]
            exact (T vs).map_update_add _ idx β₁ β₂
        have h3' : ∑ j, T vs (Function.update (Function.update αs idx (β₁ + β₂)) j
              (nabla_dual emb conn ha hl X (Function.update αs idx (β₁ + β₂) j))) =
            ∑ j, T vs (Function.update (Function.update αs idx β₁) j
              (nabla_dual emb conn ha hl X (Function.update αs idx β₁ j))) +
            ∑ j, T vs (Function.update (Function.update αs idx β₂) j
              (nabla_dual emb conn ha hl X (Function.update αs idx β₂ j))) := by
          conv_lhs => arg 2; ext j; rw [h3 j]
          exact Finset.sum_add_distrib
        
        conv_lhs => arg 2; arg 2; ext j; rw [h3 j]
        rw [Finset.sum_add_distrib]; ring
      map_update_smul' := by
        intro inst αs idx c β
        have : inst = instDecidableEqFin r := Subsingleton.elim _ _; subst this
        simp only [smul_eq_mul]
        have hF : T vs (Function.update αs idx (c • β)) =
            c * T vs (Function.update αs idx β) := by
          have := (T vs).map_update_smul αs idx c β; rwa [smul_eq_mul] at this
        rw [hF, embed_leibniz' emb X]
        
        have h_vec : ∀ i, T (Function.update vs i (conn X (vs i)))
            (Function.update αs idx (c • β)) =
            c * T (Function.update vs i (conn X (vs i))) (Function.update αs idx β) := by
          intro i
          have := (T (Function.update vs i (conn X (vs i)))).map_update_smul αs idx c β
          rwa [smul_eq_mul] at this
        simp_rw [h_vec, ← Finset.mul_sum]
        
        
        
        let f_cov := fun j => T vs (Function.update (Function.update αs idx (c • β)) j
              (nabla_dual emb conn ha hl X (Function.update αs idx (c • β) j)))
        let g_cov := fun j => T vs (Function.update (Function.update αs idx β) j
              (nabla_dual emb conn ha hl X (Function.update αs idx β j)))
        have h_ne : ∀ j, j ≠ idx → f_cov j = c * g_cov j := by
          intro j hj
          change T vs (Function.update (Function.update αs idx (c • β)) j
              (nabla_dual emb conn ha hl X (Function.update αs idx (c • β) j))) =
            c * T vs (Function.update (Function.update αs idx β) j
              (nabla_dual emb conn ha hl X (Function.update αs idx β j)))
          rw [Function.update_of_ne hj, Function.update_of_ne hj,
              Function.update_comm (Ne.symm hj) _ _ αs,
              Function.update_comm (Ne.symm hj) _ _ αs]
          have := (T vs).map_update_smul (Function.update αs j
            (nabla_dual emb conn ha hl X (αs j))) idx c β
          rwa [smul_eq_mul] at this
        have h_eq : f_cov idx =
            (emb.embed X) c * T vs (Function.update αs idx β) +
            c * g_cov idx := by
          change T vs (Function.update (Function.update αs idx (c • β)) idx
              (nabla_dual emb conn ha hl X (Function.update αs idx (c • β) idx))) =
            (emb.embed X) c * T vs (Function.update αs idx β) +
            c * T vs (Function.update (Function.update αs idx β) idx
              (nabla_dual emb conn ha hl X (Function.update αs idx β idx)))
          simp only [Function.update_self, Function.update_idem]
          rw [nabla_dual_leibniz,
              (T vs).map_update_add αs idx (c • nabla_dual emb conn ha hl X β)
                ((emb.embed X) c • β),
              (T vs).map_update_smul αs idx c (nabla_dual emb conn ha hl X β),
              (T vs).map_update_smul αs idx ((emb.embed X) c) β]
          simp [smul_eq_mul]; ring
        have h_sum := finset_sum_correction idx c
          ((emb.embed X) c * T vs (Function.update αs idx β))
          f_cov g_cov h_ne h_eq
        change _ = c * _
        rw [h_sum]; ring }
  map_update_add' := by

    intro inst vs idx v₁ v₂
    have : inst = instDecidableEqFin s := Subsingleton.elim _ _; subst this
    ext αs
    simp only [MultilinearMap.coe_mk, MultilinearMap.add_apply]
    
    rw [(T.map_update_add vs idx v₁ v₂ : T (Function.update vs idx (v₁ + v₂)) =
      T (Function.update vs idx v₁) + T (Function.update vs idx v₂))]
    simp only [MultilinearMap.add_apply, map_add]
    
    have h_vec : ∀ i,
        T (Function.update (Function.update vs idx (v₁ + v₂)) i
          (conn X (Function.update vs idx (v₁ + v₂) i))) αs =
        T (Function.update (Function.update vs idx v₁) i
          (conn X (Function.update vs idx v₁ i))) αs +
        T (Function.update (Function.update vs idx v₂) i
          (conn X (Function.update vs idx v₂ i))) αs := by
      intro i; by_cases hi : i = idx
      · subst hi; simp only [Function.update_self, Function.update_idem, ha X v₁ v₂]
        exact congr_arg (· αs) (T.map_update_add vs i _ _)
      · rw [Function.update_of_ne hi, Function.update_of_ne hi, Function.update_of_ne hi,
            Function.update_comm (Ne.symm hi) _ _ vs,
            Function.update_comm (Ne.symm hi) _ _ vs,
            Function.update_comm (Ne.symm hi) _ _ vs]
        exact congr_arg (· αs) (T.map_update_add _ idx _ _)
    simp_rw [h_vec, Finset.sum_add_distrib]
    
    have h_cov : ∀ j,
        T (Function.update vs idx (v₁ + v₂)) (Function.update αs j
          (nabla_dual emb conn ha hl X (αs j))) =
        T (Function.update vs idx v₁) (Function.update αs j
          (nabla_dual emb conn ha hl X (αs j))) +
        T (Function.update vs idx v₂) (Function.update αs j
          (nabla_dual emb conn ha hl X (αs j))) := by
      intro j
      have := T.map_update_add vs idx v₁ v₂
      change (T (Function.update vs idx (v₁ + v₂))) _ = _
      rw [this]; simp [MultilinearMap.add_apply]
    ring
  map_update_smul' := by
    intro inst vs idx c v
    have : inst = instDecidableEqFin s := Subsingleton.elim _ _; subst this
    ext αs
    simp only [MultilinearMap.coe_mk, MultilinearMap.smul_apply, smul_eq_mul]
    
    have hT : T (Function.update vs idx (c • v)) = c • T (Function.update vs idx v) :=
      T.map_update_smul vs idx c v
    rw [hT]; simp only [MultilinearMap.smul_apply, smul_eq_mul]
    
    rw [embed_leibniz' emb X]
    
    
    
    
    
    
    
    let f_vec := fun i => T (Function.update (Function.update vs idx (c • v)) i
          (conn X (Function.update vs idx (c • v) i))) αs
    let g_vec := fun i => T (Function.update (Function.update vs idx v) i
          (conn X (Function.update vs idx v i))) αs
    have h_ne : ∀ i, i ≠ idx → f_vec i = c * g_vec i := by
      intro i hi
      change T (Function.update (Function.update vs idx (c • v)) i
          (conn X (Function.update vs idx (c • v) i))) αs =
        c * T (Function.update (Function.update vs idx v) i
          (conn X (Function.update vs idx v i))) αs
      rw [Function.update_of_ne hi, Function.update_of_ne hi,
          Function.update_comm (Ne.symm hi) _ _ vs,
          Function.update_comm (Ne.symm hi) _ _ vs]
      exact congr_arg (· αs) (T.map_update_smul _ idx c v)
    have h_eq : f_vec idx =
        (emb.embed X) c * (T (Function.update vs idx v)) αs +
        c * g_vec idx := by
      change T (Function.update (Function.update vs idx (c • v)) idx
          (conn X (Function.update vs idx (c • v) idx))) αs =
        (emb.embed X) c * (T (Function.update vs idx v)) αs +
        c * T (Function.update (Function.update vs idx v) idx
          (conn X (Function.update vs idx v idx))) αs
      simp only [Function.update_self, Function.update_idem, hl X c v]
      have h1 := T.map_update_add vs idx ((emb.embed X) c • v) (c • conn X v)
      have h2 := congr_arg (· αs) h1
      simp only [MultilinearMap.add_apply] at h2; rw [h2]
      have h3 := congr_arg (· αs) (T.map_update_smul vs idx ((emb.embed X) c) v)
      simp only [MultilinearMap.smul_apply, smul_eq_mul] at h3; rw [h3]
      have h4 := congr_arg (· αs) (T.map_update_smul vs idx c (conn X v))
      simp only [MultilinearMap.smul_apply, smul_eq_mul] at h4; rw [h4]
    have h_sum := finset_sum_correction idx c
      ((emb.embed X) c * (T (Function.update vs idx v)) αs)
      f_vec g_vec h_ne h_eq
    
    rw [← Finset.mul_sum]
    change _ = c * _
    rw [h_sum]; ring





theorem nabla_tensor_eval (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) {r s : ℕ} (T : TensorData R V r s) (vs αs) :
    nabla_tensor emb conn ha hl X T vs αs =
    (emb.embed X) (T vs αs)
    - ∑ i : Fin s, T (Function.update vs i (conn X (vs i))) αs
    - ∑ j : Fin r, T vs (Function.update αs j
        (nabla_dual emb conn ha hl X (αs j)))  := by sorry

theorem nabla_scalar (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) (T : TensorData R V 0 0) :
    nabla_tensor emb conn ha hl X T ![] ![] = (emb.embed X) (T ![] ![])  := by sorry

theorem nabla_add (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) {r s : ℕ} (T₁ T₂ : TensorData R V r s) :
    nabla_tensor emb conn ha hl X (T₁ + T₂) =
    nabla_tensor emb conn ha hl X T₁ + nabla_tensor emb conn ha hl X T₂  := by sorry

theorem nabla_smul (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) {r s : ℕ} (c : R) (T : TensorData R V r s) (vs αs) :
    nabla_tensor emb conn ha hl X (c • T) vs αs =
    (emb.embed X) c * T vs αs + c * nabla_tensor emb conn ha hl X T vs αs  := by sorry

theorem nabla_smul_left (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (f : R) (X : V) {r s : ℕ} (T : TensorData R V r s) (vs αs) :
    nabla_tensor emb conn ha hl (f • X) T vs αs =
    f * nabla_tensor emb conn ha hl X T vs αs  := by sorry

theorem nabla_vector (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X Y : V) :
    nabla_tensor emb conn ha hl X (vectorToData (R := R) Y) =
    vectorToData (R := R) (conn X Y)  := by sorry

theorem nabla_add_left (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (conn_add_left : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X Y : V) {r s : ℕ} (T : TensorData R V r s) (vs αs) :
    nabla_tensor emb conn ha hl (X + Y) T vs αs =
    nabla_tensor emb conn ha hl X T vs αs +
    nabla_tensor emb conn ha hl Y T vs αs  := by sorry

theorem nabla_delta (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) :
    nabla_tensor emb conn ha hl X (delta_tensor : TensorData R V 1 1) = 0  := by sorry

theorem nabla_swap (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) {r s : ℕ} (i j : Fin s) (T : TensorData R V r s) (vs αs) :
    nabla_tensor emb conn ha hl X (swap_covariant i j T) vs αs =
    swap_covariant i j (nabla_tensor emb conn ha hl X T) vs αs  := by sorry

theorem nabla_tensor_prod (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) {r₁ s₁ r₂ s₂ : ℕ}
    (T₁ : TensorData R V r₁ s₁) (T₂ : TensorData R V r₂ s₂) :
    nabla_tensor emb conn ha hl X (tensor_prod T₁ T₂) =
    tensor_prod (nabla_tensor emb conn ha hl X T₁) T₂ +
    tensor_prod T₁ (nabla_tensor emb conn ha hl X T₂)  := by sorry

theorem nabla_contract (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V)
    (h_ntr : NablaTrComm emb atr conn ha hl)
    (X : V) (L : V →ₗ[R] V) :
    (emb.embed X) (atr.tr L) = atr.tr (commutatorEndo
      (emb.embed X).toFun (conn X) (ha X) (hl X) L)  := by sorry

end NablaTensor
