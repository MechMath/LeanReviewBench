




import dep.DifferentialGeometry.Tensor.Alternating.Shuffle.Split
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Group
open DifferentialGeometry

namespace ContinuousAlternatingMap

variable {m n : ℕ}

theorem shuffle_side_well_defined
    {σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1))}
    (τ : (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range) :
    (∃ k, σ⁻¹ (Sum.inl 0) = Sum.inl k) ↔
    (∃ k, ((σ * ↑τ)⁻¹ (Sum.inl 0)) = Sum.inl k)  := by sorry

theorem shuffle_side_well_defined_right
    {σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1))}
    (τ : (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range) :
    (∃ k, σ⁻¹ (Sum.inl 0) = Sum.inr k) ↔
    (∃ k, ((σ * ↑τ)⁻¹ (Sum.inl 0)) = Sum.inr k)  := by sorry

noncomputable def finSuccSumOptionEquiv {m n : ℕ} :
    Fin (m + 1) ⊕ Fin (n + 1) ≃ Option (Fin m ⊕ Fin (n + 1)) :=
  (Equiv.sumCongr (finSuccEquiv' 0) (Equiv.refl _)).trans ShuffleSplit.optionSumEquiv

@[simp] theorem finSuccSumOptionEquiv_inl_zero {m n : ℕ} :
    (finSuccSumOptionEquiv : Fin (m + 1) ⊕ Fin (n + 1) ≃ _)
      (Sum.inl (0 : Fin (m + 1))) = none  := by sorry

@[simp] theorem finSuccSumOptionEquiv_symm_none {m n : ℕ} :
    (finSuccSumOptionEquiv : Fin (m + 1) ⊕ Fin (n + 1) ≃ _).symm none =
      Sum.inl 0  := by sorry

def normalizeLeft (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (k : Fin (m + 1)) :
    Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)) :=
  σ * Equiv.Perm.sumCongr (Equiv.swap 0 k) 1

theorem normalizeLeft_fixes (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (k : Fin (m + 1)) (hk : σ⁻¹ (Sum.inl 0) = Sum.inl k) :
    normalizeLeft σ k (Sum.inl 0) = Sum.inl 0  := by sorry

theorem normalizeLeft_coset (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (k : Fin (m + 1)) :
    Quotient.mk'' (normalizeLeft σ k) =
      (Quotient.mk'' σ : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin (n + 1)))  := by sorry

noncomputable def restrictComplement
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1))) :
    Equiv.Perm (Fin m ⊕ Fin (n + 1)) :=
  Equiv.removeNone (Equiv.permCongr finSuccSumOptionEquiv σ)

theorem restrictComplement_sign
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hfix : σ (Sum.inl 0) = Sum.inl 0) :
    Equiv.Perm.sign (restrictComplement σ) = Equiv.Perm.sign σ  := by sorry

theorem restrictComplement_sumCongr_mem
    (τ_l : Equiv.Perm (Fin (m + 1))) (τ_r : Equiv.Perm (Fin (n + 1)))
    (hτ_fix : τ_l 0 = 0) :
    restrictComplement (Equiv.Perm.sumCongr τ_l τ_r) ∈
      (Equiv.Perm.sumCongrHom (Fin m) (Fin (n + 1))).range  := by sorry

noncomputable def shuffleLeftRestrictRepresentative
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hσ : ∃ k, σ⁻¹ (Sum.inl 0) = Sum.inl k) :
    Equiv.Perm (Fin m ⊕ Fin (n + 1)) :=
  let k := hσ.choose
  restrictComplement (normalizeLeft σ k)

theorem shuffleLeftRestrictRepresentative_respects_leftRel
    (σ₁ σ₂ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hσ₁ : ∃ k, σ₁⁻¹ (Sum.inl 0) = Sum.inl k)
    (hσ₂ : ∃ k, σ₂⁻¹ (Sum.inl 0) = Sum.inl k)
    (h_rel : QuotientGroup.leftRel
        (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range σ₁ σ₂) :
    QuotientGroup.leftRel
        (Equiv.Perm.sumCongrHom (Fin m) (Fin (n + 1))).range
        (shuffleLeftRestrictRepresentative σ₁ hσ₁) (shuffleLeftRestrictRepresentative σ₂ hσ₂)  := by sorry

noncomputable def shuffleLeftExtendRepresentative
    (σ' : Equiv.Perm (Fin m ⊕ Fin (n + 1))) :
    Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)) :=
  Equiv.permCongr finSuccSumOptionEquiv.symm σ'.optionCongr

theorem shuffleLeftExtendRepresentative_fixes (σ' : Equiv.Perm (Fin m ⊕ Fin (n + 1))) :
    shuffleLeftExtendRepresentative σ' (Sum.inl 0) = Sum.inl 0  := by sorry

theorem shuffleLeftExtendRepresentative_isLeft (σ' : Equiv.Perm (Fin m ⊕ Fin (n + 1))) :
    ∃ k, (shuffleLeftExtendRepresentative σ')⁻¹ (Sum.inl 0) = Sum.inl k  := by sorry

theorem restrictComplement_shuffleLeftExtendRepresentative
    (σ' : Equiv.Perm (Fin m ⊕ Fin (n + 1))) :
    restrictComplement (shuffleLeftExtendRepresentative σ') = σ'  := by sorry

theorem shuffleLeftExtendRepresentative_restrictComplement
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hfix : σ (Sum.inl 0) = Sum.inl 0) :
    shuffleLeftExtendRepresentative (restrictComplement σ) = σ  := by sorry

noncomputable def liftPermSucc (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin (m + 1)) :=
  Equiv.permCongr (finSuccEquiv' 0).symm τ.optionCongr

theorem shuffleLeftExtendRepresentative_respects_leftRel
    (s1 s2 : Equiv.Perm (Fin m ⊕ Fin (n + 1)))
    (h_rel : QuotientGroup.leftRel
        (Equiv.Perm.sumCongrHom (Fin m) (Fin (n + 1))).range s1 s2) :
    QuotientGroup.leftRel
        (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range
        (shuffleLeftExtendRepresentative s1) (shuffleLeftExtendRepresentative s2)  := by sorry

theorem shuffleLeftRestrictRepresentative_extendRepresentative
    (σ' : Equiv.Perm (Fin m ⊕ Fin (n + 1))) :
    shuffleLeftRestrictRepresentative (shuffleLeftExtendRepresentative σ') (shuffleLeftExtendRepresentative_isLeft σ') = σ'  := by sorry

theorem shuffleLeftExtendRepresentative_restrictRepresentative_rel
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hσ : ∃ k, σ⁻¹ (Sum.inl 0) = Sum.inl k) :
    QuotientGroup.leftRel
        (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range
        (shuffleLeftExtendRepresentative (shuffleLeftRestrictRepresentative σ hσ)) σ  := by sorry

noncomputable def shuffleLeftRestrict :
    {σ : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin (n + 1)) //
      ∀ τ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)),
        Quotient.mk'' τ = σ → ∃ k, τ⁻¹ (Sum.inl 0) = Sum.inl k} ≃
    Equiv.Perm.ModSumCongr (Fin m) (Fin (n + 1)) where
  toFun := fun ⟨q, hq⟩ =>
    Quotient.mk'' (shuffleLeftRestrictRepresentative q.out (hq _ (Quotient.out_eq q)))
  invFun := fun q =>
    ⟨Quotient.mk'' (shuffleLeftExtendRepresentative q.out), fun τ hτ => by
      have h_rel := QuotientGroup.leftRel_apply.mp (Quotient.exact' hτ)
      have h_inv : (shuffleLeftExtendRepresentative q.out)⁻¹ * τ ∈
          (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range := by
        rw [show (shuffleLeftExtendRepresentative q.out)⁻¹ * τ = (τ⁻¹ * shuffleLeftExtendRepresentative q.out)⁻¹
          from by group]
        exact Subgroup.inv_mem _ h_rel
      rw [show τ = shuffleLeftExtendRepresentative q.out * ((shuffleLeftExtendRepresentative q.out)⁻¹ * τ)
        from by group]
      exact (shuffle_side_well_defined
        (σ := shuffleLeftExtendRepresentative q.out) ⟨_, h_inv⟩).mp
        (shuffleLeftExtendRepresentative_isLeft q.out)⟩
  left_inv := fun ⟨q, hq⟩ => by
    ext
    have h1 : (Quotient.mk'' (shuffleLeftRestrictRepresentative q.out
        (hq _ (Quotient.out_eq q))) :
        Equiv.Perm.ModSumCongr (Fin m) (Fin (n + 1))) =
      Quotient.mk'' (Quotient.mk'' (shuffleLeftRestrictRepresentative q.out
        (hq _ (Quotient.out_eq q)))).out :=
      (Quotient.out_eq _).symm
    calc Quotient.mk'' (shuffleLeftExtendRepresentative (Quotient.mk''
            (shuffleLeftRestrictRepresentative q.out (hq _ (Quotient.out_eq q)))).out)
        = Quotient.mk'' (shuffleLeftExtendRepresentative
            (shuffleLeftRestrictRepresentative q.out (hq _ (Quotient.out_eq q)))) :=
          Quotient.sound' (shuffleLeftExtendRepresentative_respects_leftRel _ _
            (Quotient.exact' h1.symm))
      _ = Quotient.mk'' q.out :=
          Quotient.sound' (shuffleLeftExtendRepresentative_restrictRepresentative_rel q.out _)
      _ = q := Quotient.out_eq q
  right_inv := fun q => by
    have h1 : (Quotient.mk'' (shuffleLeftExtendRepresentative q.out) :
        Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin (n + 1))) =
      Quotient.mk'' (Quotient.mk'' (shuffleLeftExtendRepresentative q.out)).out :=
      (Quotient.out_eq _).symm
    calc Quotient.mk'' (shuffleLeftRestrictRepresentative
            (Quotient.mk'' (shuffleLeftExtendRepresentative q.out)).out _)
        = Quotient.mk'' (shuffleLeftRestrictRepresentative (shuffleLeftExtendRepresentative q.out)
            (shuffleLeftExtendRepresentative_isLeft q.out)) :=
          Quotient.sound' (shuffleLeftRestrictRepresentative_respects_leftRel _ _ _ _
            (Quotient.exact' h1.symm))
      _ = Quotient.mk'' q.out := by rw [shuffleLeftRestrictRepresentative_extendRepresentative]
      _ = q := Quotient.out_eq q

theorem shuffleLeftRestrict_subtype_of_inv
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hσ : ∃ k, σ⁻¹ (Sum.inl 0) = Sum.inl k)
    (τ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hτ : (Quotient.mk'' τ : Equiv.Perm.ModSumCongr _ _) = Quotient.mk'' σ) :
    ∃ k, τ⁻¹ (Sum.inl 0) = Sum.inl k  := by sorry

@[simp] theorem finSuccSumOptionEquiv_symm_some
    (z : Fin m ⊕ Fin (n + 1)) :
    (finSuccSumOptionEquiv : Fin (m + 1) ⊕ Fin (n + 1) ≃ _).symm (some z) =
      Sum.map Fin.succ id z  := by sorry

theorem restrictComplement_lift
    (ν : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hν : ν (Sum.inl 0) = Sum.inl 0)
    (y : Fin m ⊕ Fin (n + 1)) :
    Sum.map Fin.succ id (restrictComplement ν y) =
      ν (Sum.map Fin.succ id y)  := by sorry

noncomputable def finSumSuccOptionEquiv {m n : ℕ} :
    Fin (m + 1) ⊕ Fin (n + 1) ≃ Option (Fin (m + 1) ⊕ Fin n) :=
  (Equiv.sumComm _ _).trans <|
    (finSuccSumOptionEquiv (m := n) (n := m)).trans <|
      Equiv.optionCongr (Equiv.sumComm _ _)

@[simp] theorem finSumSuccOptionEquiv_inr_zero {m n : ℕ} :
    (finSumSuccOptionEquiv : Fin (m + 1) ⊕ Fin (n + 1) ≃ _)
      (Sum.inr (0 : Fin (n + 1))) = none  := by sorry

@[simp] theorem finSumSuccOptionEquiv_symm_none {m n : ℕ} :
    (finSumSuccOptionEquiv : Fin (m + 1) ⊕ Fin (n + 1) ≃ _).symm none =
      Sum.inr 0  := by sorry

@[simp] theorem finSumSuccOptionEquiv_inl {m n : ℕ} (a : Fin (m + 1)) :
    (finSumSuccOptionEquiv : Fin (m + 1) ⊕ Fin (n + 1) ≃ _) (Sum.inl a) =
      some (Sum.inl a)  := by sorry

@[simp] theorem finSumSuccOptionEquiv_inr_succ {m n : ℕ}
    (b : Fin n) :
    (finSumSuccOptionEquiv : Fin (m + 1) ⊕ Fin (n + 1) ≃ _)
      (Sum.inr b.succ) = some (Sum.inr b)  := by sorry

@[simp] theorem finSumSuccOptionEquiv_symm_some_inl {m n : ℕ}
    (a : Fin (m + 1)) :
    (finSumSuccOptionEquiv : Fin (m + 1) ⊕ Fin (n + 1) ≃ _).symm
      (some (Sum.inl a)) = Sum.inl a  := by sorry

@[simp] theorem finSumSuccOptionEquiv_symm_some_inr {m n : ℕ}
    (b : Fin n) :
    (finSumSuccOptionEquiv : Fin (m + 1) ⊕ Fin (n + 1) ≃ _).symm
      (some (Sum.inr b)) = Sum.inr b.succ  := by sorry

def normalizeRight (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (k : Fin (n + 1)) :
    Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)) :=
  Equiv.swap (Sum.inl 0) (Sum.inr 0) *
    σ * Equiv.Perm.sumCongr 1 (Equiv.swap 0 k)

theorem normalizeRight_fixes (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (k : Fin (n + 1)) (hk : σ⁻¹ (Sum.inl 0) = Sum.inr k) :
    normalizeRight σ k (Sum.inr 0) = Sum.inr 0  := by sorry

noncomputable def restrictComplementRight
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1))) :
    Equiv.Perm (Fin (m + 1) ⊕ Fin n) :=
  Equiv.removeNone (Equiv.permCongr finSumSuccOptionEquiv σ)

theorem restrictComplementRight_sign
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hfix : σ (Sum.inr 0) = Sum.inr 0) :
    Equiv.Perm.sign (restrictComplementRight σ) = Equiv.Perm.sign σ  := by sorry

theorem restrictComplementRight_lift
    (ν : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hν : ν (Sum.inr 0) = Sum.inr 0)
    (y : Fin (m + 1) ⊕ Fin n) :
    Sum.map id Fin.succ (restrictComplementRight ν y) =
      ν (Sum.map id Fin.succ y)  := by sorry

noncomputable def shuffleRightRestrictRepresentative
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hσ : ∃ k, σ⁻¹ (Sum.inl 0) = Sum.inr k) :
    Equiv.Perm (Fin (m + 1) ⊕ Fin n) :=
  let k := hσ.choose
  restrictComplementRight (normalizeRight σ k)

noncomputable def shuffleRightExtendRepresentative
    (σ' : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) :
    Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)) :=
  Equiv.swap (Sum.inl 0) (Sum.inr 0) *
    Equiv.permCongr finSumSuccOptionEquiv.symm σ'.optionCongr

theorem shuffleRightExtendRepresentative_isRight (σ' : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) :
    ∃ k, (shuffleRightExtendRepresentative σ')⁻¹ (Sum.inl 0) = Sum.inr k  := by sorry

theorem restrictComplementRight_sumCongr_mem
    (τ_l : Equiv.Perm (Fin (m + 1))) (τ_r : Equiv.Perm (Fin (n + 1)))
    (hτ_fix : τ_r 0 = 0) :
    restrictComplementRight (Equiv.Perm.sumCongr τ_l τ_r) ∈
      (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin n)).range  := by sorry

theorem shuffleRightRestrictRepresentative_respects_leftRel
    (σ₁ σ₂ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hσ₁ : ∃ k, σ₁⁻¹ (Sum.inl 0) = Sum.inr k)
    (hσ₂ : ∃ k, σ₂⁻¹ (Sum.inl 0) = Sum.inr k)
    (h_rel : QuotientGroup.leftRel
        (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range σ₁ σ₂) :
    QuotientGroup.leftRel
        (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin n)).range
        (shuffleRightRestrictRepresentative σ₁ hσ₁) (shuffleRightRestrictRepresentative σ₂ hσ₂)  := by sorry

noncomputable def liftPermSuccR (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  Equiv.permCongr (finSuccEquiv' 0).symm τ.optionCongr

theorem shuffleRightExtendRepresentative_respects_leftRel
    (σ₁' σ₂' : Equiv.Perm (Fin (m + 1) ⊕ Fin n))
    (h_rel : QuotientGroup.leftRel
        (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin n)).range σ₁' σ₂') :
    QuotientGroup.leftRel
        (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range
        (shuffleRightExtendRepresentative σ₁') (shuffleRightExtendRepresentative σ₂')  := by sorry

theorem restrictComplementRight_shuffleRightExtendRepresentative
    (σ' : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) :
    restrictComplementRight
      (Equiv.permCongr finSumSuccOptionEquiv.symm σ'.optionCongr) = σ'  := by sorry

theorem shuffleRightRestrictRepresentative_extendRepresentative
    (σ' : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) :
    shuffleRightRestrictRepresentative (shuffleRightExtendRepresentative σ') (shuffleRightExtendRepresentative_isRight σ') = σ'  := by sorry

theorem shuffleRightExtendRepresentative_restrictComplementRight
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hfix : σ (Sum.inr 0) = Sum.inr 0) :
    shuffleRightExtendRepresentative (restrictComplementRight σ) =
      Equiv.swap (Sum.inl 0) (Sum.inr 0) * σ  := by sorry

theorem shuffleRightExtendRepresentative_restrictRepresentative_rel
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hσ : ∃ k, σ⁻¹ (Sum.inl 0) = Sum.inr k) :
    QuotientGroup.leftRel
        (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range
        (shuffleRightExtendRepresentative (shuffleRightRestrictRepresentative σ hσ)) σ  := by sorry

noncomputable def shuffleRightRestrict :
    {σ : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin (n + 1)) //
      ∀ τ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)),
        Quotient.mk'' τ = σ → ∃ k, τ⁻¹ (Sum.inl 0) = Sum.inr k} ≃
    Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n) where
  toFun := fun ⟨q, hq⟩ =>
    Quotient.mk'' (shuffleRightRestrictRepresentative q.out (hq _ (Quotient.out_eq q)))
  invFun := fun q =>
    ⟨Quotient.mk'' (shuffleRightExtendRepresentative q.out), fun τ hτ => by
      have h_rel := QuotientGroup.leftRel_apply.mp (Quotient.exact' hτ)
      have h_inv : (shuffleRightExtendRepresentative q.out)⁻¹ * τ ∈
          (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range := by
        rw [show (shuffleRightExtendRepresentative q.out)⁻¹ * τ =
          (τ⁻¹ * shuffleRightExtendRepresentative q.out)⁻¹ from by group]
        exact Subgroup.inv_mem _ h_rel
      rw [show τ = shuffleRightExtendRepresentative q.out *
        ((shuffleRightExtendRepresentative q.out)⁻¹ * τ) from by group]
      exact (shuffle_side_well_defined_right
        (σ := shuffleRightExtendRepresentative q.out) ⟨_, h_inv⟩).mp
        (shuffleRightExtendRepresentative_isRight q.out)⟩
  left_inv := fun ⟨q, hq⟩ => by
    ext
    have h1 := (Quotient.out_eq (Quotient.mk'' (shuffleRightRestrictRepresentative q.out
        (hq _ (Quotient.out_eq q))) :
        Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n))).symm
    calc Quotient.mk'' (shuffleRightExtendRepresentative (Quotient.mk''
            (shuffleRightRestrictRepresentative q.out (hq _ (Quotient.out_eq q)))).out)
        = Quotient.mk'' (shuffleRightExtendRepresentative
            (shuffleRightRestrictRepresentative q.out (hq _ (Quotient.out_eq q)))) :=
          Quotient.sound' (shuffleRightExtendRepresentative_respects_leftRel _ _ (Quotient.exact' h1.symm))
      _ = Quotient.mk'' q.out :=
          Quotient.sound' (shuffleRightExtendRepresentative_restrictRepresentative_rel q.out _)
      _ = q := Quotient.out_eq q
  right_inv := fun q => by
    have h1 := (Quotient.out_eq (Quotient.mk'' (shuffleRightExtendRepresentative q.out) :
        Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin (n + 1)))).symm
    calc Quotient.mk'' (shuffleRightRestrictRepresentative
            (Quotient.mk'' (shuffleRightExtendRepresentative q.out)).out _)
        = Quotient.mk'' (shuffleRightRestrictRepresentative (shuffleRightExtendRepresentative q.out)
            (shuffleRightExtendRepresentative_isRight q.out)) :=
          Quotient.sound' (shuffleRightRestrictRepresentative_respects_leftRel _ _ _ _
            (Quotient.exact' h1.symm))
      _ = Quotient.mk'' q.out := by rw [shuffleRightRestrictRepresentative_extendRepresentative]
      _ = q := Quotient.out_eq q

theorem shuffleRightRestrict_subtype_of_inv
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hσ : ∃ k, σ⁻¹ (Sum.inl 0) = Sum.inr k)
    (τ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hτ : (Quotient.mk'' τ : Equiv.Perm.ModSumCongr _ _) = Quotient.mk'' σ) :
    ∃ k, τ⁻¹ (Sum.inl 0) = Sum.inr k  := by sorry

end ContinuousAlternatingMap

