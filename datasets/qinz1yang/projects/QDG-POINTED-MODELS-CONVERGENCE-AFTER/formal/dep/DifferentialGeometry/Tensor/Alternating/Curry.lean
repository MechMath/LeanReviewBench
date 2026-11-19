





import dep.DifferentialGeometry.Tensor.Alternating.Flip
import dep.DifferentialGeometry.Tensor.Alternating.Composition
import dep.DifferentialGeometry.Tensor.Alternating.Reindexing.Domain
import dep.DifferentialGeometry.Tensor.Alternating.Shuffle.Decomposition
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Tactic.Cases

namespace ContinuousAlternatingMap

noncomputable section curry

variable {𝕜 E F G ι ι' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [Fintype ι] [Fintype ι']
  {m n : ℕ}

def uncurryFin (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) : E [⋀^Fin (n + 1)]→L[𝕜] F :=
  AlternatingMap.mkContinuous (.alternatizeUncurryFin <| toAlternatingMapLinear ∘ₗ f)
    ((n + 1) * ‖f‖) fun v ↦ calc
      _ = ‖∑ k, (-1) ^ k.val • f (v k) (k.removeNth v)‖ := by
        simp [AlternatingMap.alternatizeUncurryFin_apply]
      _ ≤ ∑ k, ‖f‖ * ‖v k‖ * ∏ j, ‖v (k.succAbove j)‖ := by
        refine norm_sum_le_of_le _ fun k _ ↦ ?_
        rw [norm_isUnit_zsmul _ (.pow _ isUnit_one.neg)]
        exact (f (v k)).le_of_opNorm_le (f.le_opNorm _) _
      _ = _ := by
        simp [mul_assoc, ← Fin.prod_univ_succAbove (‖v ·‖)]

lemma toAlternatingMap_uncurryFin (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    (uncurryFin f).toAlternatingMap = .alternatizeUncurryFin (toAlternatingMapLinear ∘ₗ f)  := by sorry

theorem norm_uncurryFin_le (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    ‖uncurryFin f‖ ≤ (n + 1) * ‖f‖  := by sorry

theorem uncurryFin_apply (f : E →L[𝕜] (E [⋀^Fin n]→L[𝕜] F)) (v : Fin (n + 1) → E) :
    uncurryFin f v = ∑ k, (-1) ^ k.val • f (v k) (k.removeNth v)  := by sorry

theorem uncurryFin_add (f g : E →L[𝕜] (E [⋀^Fin n]→L[𝕜] F)) :
    uncurryFin (f + g) = uncurryFin f + uncurryFin g  := by sorry

theorem uncurryFin_smul {M : Type*} [Monoid M] [DistribMulAction M F] [ContinuousConstSMul M F]
    [SMulCommClass 𝕜 M F] (c : M) (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    uncurryFin (c • f) = c • uncurryFin f  := by sorry

@[simps! apply]
def uncurryFinCLM :
    (E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) →L[𝕜] E [⋀^Fin (n + 1)]→L[𝕜] F :=
  LinearMap.mkContinuous
    { toFun := uncurryFin (𝕜 := 𝕜) (E := E) (F := F) (n := n)
      map_add' := by exact uncurryFin_add
      map_smul' := by exact uncurryFin_smul }
    (n + 1) norm_uncurryFin_le

theorem uncurryFin_uncurryFinCLM_comp_of_symmetric {f : E →L[𝕜] E →L[𝕜] E [⋀^Fin n]→L[𝕜] F}
    (hf : ∀ x y, f x y = f y x) :
    uncurryFin (uncurryFinCLM.comp f) = 0  := by sorry

def curryFin (f : E [⋀^Fin (n + 1)]→L[𝕜] F) : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F :=
  f.curryLeft

theorem curryFin_apply (f : E [⋀^Fin (n + 1)]→L[𝕜] F) (x : E) (m : Fin n → E) :
    curryFin f x m = f (Fin.cons x m)  := by sorry

theorem norm_curryFin_le (f : E [⋀^Fin (n + 1)]→L[𝕜] F) :
    ‖curryFin f‖ ≤ ‖f‖  := by sorry

theorem curryFin_add (f g : E [⋀^Fin (n + 1)]→L[𝕜] F) :
    curryFin (f + g) = curryFin f + curryFin g  := by sorry

theorem curryFin_smul {M : Type*} [Monoid M] [DistribMulAction M F] [ContinuousConstSMul M F]
    [SMulCommClass 𝕜 M F] (c : M) (f : E [⋀^Fin (n + 1)]→L[𝕜] F) :
    curryFin (c • f) = c • curryFin f  := by sorry

theorem uncurryFin_curryFin (f : E [⋀^Fin (n + 1)]→L[𝕜] F) :
    uncurryFin (curryFin f) = (n + 1 : ℕ) • f  := by sorry

def curryFinRight
    (F : E [⋀^Fin (m + 1)]→L[𝕜] E [⋀^Fin (n + 1)]→L[𝕜] G) (x : E) :
    E [⋀^Fin (m + 1)]→L[𝕜] E [⋀^Fin n]→L[𝕜] G :=
  let g : (E [⋀^Fin (n + 1)]→L[𝕜] G) →L[𝕜] (E [⋀^Fin n]→L[𝕜] G) :=
    LinearMap.mkContinuous
      { toFun := fun f => curryFin f x
        map_add' := fun f₁ f₂ => by rw [curryFin_add]; rfl
        map_smul' := fun c f => by rw [curryFin_smul]; rfl }
      ‖x‖
      (fun f => by
        change ‖curryFin f x‖ ≤ ‖x‖ * ‖f‖
        calc ‖curryFin f x‖
            ≤ ‖curryFin f‖ * ‖x‖ := (curryFin f).le_opNorm x
          _ ≤ ‖f‖ * ‖x‖ := by
              exact mul_le_mul_of_nonneg_right (norm_curryFin_le f) (norm_nonneg _)
          _ = ‖x‖ * ‖f‖ := by ring)
  g.compContinuousAlternatingMap F

@[simp] theorem curryFinRight_apply
    (F : E [⋀^Fin (m + 1)]→L[𝕜] E [⋀^Fin (n + 1)]→L[𝕜] G)
    (x : E) (v : Fin (m + 1) → E) (w : Fin n → E) :
    curryFinRight F x v w = F v (Fin.cons x w)  := by sorry

variable [DecidableEq ι] [DecidableEq ι']

def uncurrySum.summand (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F) (σ : Equiv.Perm.ModSumCongr ι ι') :
    ContinuousMultilinearMap 𝕜 (fun _ : ι ⊕ ι' => E) F :=
  Quotient.liftOn' σ
    (fun σ =>
      Equiv.Perm.sign σ •
        (ContinuousMultilinearMap.uncurrySum
          (f.toContinuousMultilinearMap.flipAlternating.toContinuousMultilinearMap.flipMultilinear)
            : ContinuousMultilinearMap 𝕜 (fun _ => E) (F)).domDomCongr σ)
    fun σ₁ σ₂ H => by
      rw [QuotientGroup.leftRel_apply] at H
      obtain ⟨⟨sl, sr⟩, h⟩ := H
      ext v
      simp only [_root_.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
        ContinuousMultilinearMap.uncurrySum_apply]
      replace h := inv_mul_eq_iff_eq_mul.mp h.symm
      have : Equiv.Perm.sign (σ₁ * Equiv.Perm.sumCongrHom _ _ (sl, sr))
        = Equiv.Perm.sign σ₁ * (Equiv.Perm.sign sl * Equiv.Perm.sign sr) := by simp
      rw [h, this, mul_smul, mul_smul, smul_left_cancel_iff, smul_comm]
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      erw [← (f.flipAlternating
        ((fun i ↦ v (σ₁ (Sum.map (⇑sl) (⇑sr) i))) ∘ Sum.inr)).map_congr_perm fun i => v (σ₁ _)]
      simp only [AlternatingMap.coe_mk, ContinuousMultilinearMap.coe_coe,
        coe_toContinuousMultilinearMap]
      erw [← (f fun i ↦ v (σ₁ (Sum.inl i))).map_congr_perm fun i => v (σ₁ _)]
      simp [ContinuousMultilinearMap.flipAlternating]
      rfl

theorem uncurrySum.summand_quot_mk
    (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F) (σ : Equiv.Perm (ι ⊕ ι')) :
    uncurrySum.summand f (Quot.mk
    (⇑(QuotientGroup.leftRel (Equiv.Perm.sumCongrHom ι ι').range)) σ) = Equiv.Perm.sign σ •
    (ContinuousMultilinearMap.uncurrySum
    (f.toContinuousMultilinearMap.flipAlternating.toContinuousMultilinearMap.flipMultilinear)
      : ContinuousMultilinearMap 𝕜 (fun _ => E) F).domDomCongr σ  := by sorry

theorem uncurrySum.summand_quotient_mk
    (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F) (σ : Equiv.Perm (ι ⊕ ι')) :
    uncurrySum.summand f (Quotient.mk'' σ) = Equiv.Perm.sign σ •
    (ContinuousMultilinearMap.uncurrySum
    (f.toContinuousMultilinearMap.flipAlternating.toContinuousMultilinearMap.flipMultilinear)
      : ContinuousMultilinearMap 𝕜 (fun _ => E) F).domDomCongr σ  := by sorry

theorem uncurrySum_summand_eval
    (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F)
    (σ : Equiv.Perm (ι ⊕ ι')) (v : ι ⊕ ι' → E) :
    uncurrySum.summand f (Quotient.mk'' σ) v =
      Equiv.Perm.sign σ • f (fun i => v (σ (Sum.inl i))) (fun i => v (σ (Sum.inr i)))  := by sorry

theorem uncurrySum.summand_add_swap_smul_eq_zero (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F)
    (σ : Equiv.Perm.ModSumCongr ι ι') {v : ι ⊕ ι' → E}
    {i j : ι ⊕ ι'} (hv : v i = v j) (hij : i ≠ j) :
    uncurrySum.summand f σ v + uncurrySum.summand f (Equiv.swap i j • σ) v = 0  := by sorry

theorem uncurrySum.summand_eq_zero_of_smul_invariant (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F)
    (σ : Equiv.Perm.ModSumCongr ι ι') {v : ι ⊕ ι' → E}
    {i j : ι ⊕ ι'} (hv : v i = v j) (hij : i ≠ j) :
    Equiv.swap i j • σ = σ → uncurrySum.summand f σ v = 0  := by sorry

def uncurrySum (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F) : E [⋀^ι ⊕ ι']→L[𝕜] F :=
    { ∑ σ : Equiv.Perm.ModSumCongr ι ι', uncurrySum.summand f σ with
    toFun := fun v => (⇑(∑ σ : Equiv.Perm.ModSumCongr ι ι', uncurrySum.summand f σ)) v
    map_eq_zero_of_eq' := fun v i j hv hij => by
      rw [_root_.sum_apply]
      exact
        Finset.sum_involution (fun σ _ => Equiv.swap i j • σ)
          (fun σ _ => uncurrySum.summand_add_swap_smul_eq_zero f σ hv hij)
          (fun σ _ => mt <| uncurrySum.summand_eq_zero_of_smul_invariant f σ hv hij)
          (fun σ _ => Finset.mem_univ _) fun σ _ =>
          Equiv.swap_smul_involutive i j σ }

theorem uncurrySum_coe (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F) :
    ((uncurrySum f).toContinuousMultilinearMap : ContinuousMultilinearMap 𝕜 (fun _ => E) F) =
      ∑ σ : Equiv.Perm.ModSumCongr ι ι', uncurrySum.summand f σ  := by sorry

theorem uncurrySum_apply (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F) (m : ι ⊕ ι' → E) :
    uncurrySum f m = (∑ σ : Equiv.Perm.ModSumCongr ι ι', uncurrySum.summand f σ) m  := by sorry

def uncurryFinAdd (f : E [⋀^Fin m]→L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    E [⋀^Fin (m + n)]→L[𝕜] F :=
  ContinuousAlternatingMap.domDomCongr finSumFinEquiv (uncurrySum f)

variable [DecidableEq ι] [DecidableEq ι']

open scoped TensorProduct

theorem lift_comp_domCoprod_eq_uncurrySum
    {N N' N'' : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
    [NormedAddCommGroup N'] [NormedSpace 𝕜 N'] [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
    (g : E [⋀^Fin m]→L[𝕜] N) (h : E [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'')
    (φ : N ⊗[𝕜] N' →ₗ[𝕜] N'') (hφ : ∀ a b, φ (a ⊗ₜ[𝕜] b) = f a b) :
    φ.compAlternatingMap (g.toAlternatingMap.domCoprod h.toAlternatingMap) =
      (uncurrySum (f.compContinuousAlternatingMap₂ g h)).toAlternatingMap  := by sorry

variable {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']

theorem summand_left_match
    (F : E [⋀^Fin (m + 1)]→L[𝕜] E [⋀^Fin (n + 1)]→L[𝕜] N'')
    (x : E) (w : Fin (m + 1) ⊕ Fin (n + 1) → E) (hw : w (Sum.inl 0) = x)
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hσ : ∃ k, σ⁻¹ (Sum.inl 0) = Sum.inl k)
    (σ' : Equiv.Perm (Fin m ⊕ Fin (n + 1)))
    (hσ' : Quotient.mk'' σ' = shuffleLeftRestrict
      ⟨Quotient.mk'' σ, shuffleLeftRestrict_subtype_of_inv σ hσ⟩) :
    uncurrySum.summand F (Quotient.mk'' σ) w =
      uncurrySum.summand (curryFin F x) (Quotient.mk'' σ') (w ∘ Sum.map Fin.succ id)  := by sorry

theorem summand_right_match
    (F : E [⋀^Fin (m + 1)]→L[𝕜] E [⋀^Fin (n + 1)]→L[𝕜] N'')
    (x : E) (w : Fin (m + 1) ⊕ Fin (n + 1) → E) (hw : w (Sum.inl 0) = x)
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hσ : ∃ k, σ⁻¹ (Sum.inl 0) = Sum.inr k)
    (σ' : Equiv.Perm (Fin (m + 1) ⊕ Fin n))
    (hσ' : Quotient.mk'' σ' =
      shuffleRightRestrict ⟨Quotient.mk'' σ,
        shuffleRightRestrict_subtype_of_inv σ hσ⟩) :
    uncurrySum.summand F (Quotient.mk'' σ) w =
      -(uncurrySum.summand (curryFinRight F x) (Quotient.mk'' σ')
        (fun y => w (Equiv.swap (Sum.inl (0 : Fin (m + 1))) (Sum.inr 0)
          (Sum.map id Fin.succ y))))  := by sorry

theorem curryFin_sum_smul_clm {κ : Type*} {p : ℕ}
    (s : Finset κ) (c : κ → 𝕜)
    (f : κ → E [⋀^Fin (p + 1)]→L[𝕜] F) :
    curryFin (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • curryFin (f i)  := by sorry

theorem curryFin_sum_smul {κ : Type*} {p : ℕ}
    (s : Finset κ) (c : κ → 𝕜)
    (f : κ → E [⋀^Fin (p + 1)]→L[𝕜] F) (x : E) :
    curryFin (∑ i ∈ s, c i • f i) x = ∑ i ∈ s, c i • curryFin (f i) x  := by sorry

end curry
end ContinuousAlternatingMap

