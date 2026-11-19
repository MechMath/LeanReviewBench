


import dep.DifferentialGeometry.Tensor.Multilinear.Bundle.TensorProduct
open DifferentialGeometry.Tensor.Multilinear

noncomputable section


open Bundle Set
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]
variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

theorem triv_coord_domDomCongr {s s' d : ℕ}
    (b : Module.Basis (Fin d) 𝕜 F)
    (e : Fin s ≃ Fin s')
    (idx : Fin s' → Fin d) (x₀ x : B)
    (α : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    (continuousMultilinearMapBasis b s').repr
      (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin s' => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 s' F E x) x₀
        ⟨x, ContinuousMultilinearMap.domDomCongr e α⟩).2 idx =
    (continuousMultilinearMapBasis b s).repr
      (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x) x₀ ⟨x, α⟩).2
        (idx ∘ e)  := by sorry

end Bundle.continuousMultilinearMap

namespace DifferentialGeometry.MultilinearSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]
variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

noncomputable def domDomCongr {s s' : ℕ} (e : Fin s ≃ Fin s')
    (α : MultilinearSection 𝕜 F IB E n s) :
    MultilinearSection 𝕜 F IB E n s' :=
  ⟨fun x => ContinuousMultilinearMap.domDomCongr e (α x), by
    let d := Module.finrank 𝕜 F
    let b : Module.Basis (Fin d) 𝕜 F := Module.finBasis 𝕜 F
    rw [contMDiff_multilinearSection_iff_coord E n b]
    intro idx x₀
    have hα := ((contMDiff_multilinearSection_iff_coord E n b
      (fun x => (α x : Bundle.continuousMultilinearMap 𝕜 s F E x))).mp α.contMDiff)
    simp_rw [Bundle.continuousMultilinearMap.triv_coord_domDomCongr b e idx x₀ _ (α _)]
    exact hα (idx ∘ e) x₀⟩

@[simp] theorem domDomCongr_apply {s s' : ℕ} (e : Fin s ≃ Fin s')
    (α : MultilinearSection 𝕜 F IB E n s) (x : B) :
    (domDomCongr (IB := IB) n e α) x = ContinuousMultilinearMap.domDomCongr e (α x)  := by sorry

@[simp] theorem domDomCongr_refl {s : ℕ} (α : MultilinearSection 𝕜 F IB E n s) :
    domDomCongr (IB := IB) n (Equiv.refl (Fin s)) α = α  := by sorry

@[simp] theorem domDomCongr_zero {s s' : ℕ} (e : Fin s ≃ Fin s') :
    domDomCongr (IB := IB) n e (0 : MultilinearSection 𝕜 F IB E n s)
      = (0 : MultilinearSection 𝕜 F IB E n s')  := by sorry

theorem domDomCongr_id_of_valPres {s : ℕ} (e : Fin s ≃ Fin s)
    (he : ∀ i, ((e i : Fin s) : ℕ) = (i : ℕ))
    (α : MultilinearSection 𝕜 F IB E n s) :
    domDomCongr (IB := IB) n e α = α  := by sorry

theorem domDomCongr_trans {s s' s'' : ℕ} (e₁ : Fin s ≃ Fin s') (e₂ : Fin s' ≃ Fin s'')
    (α : MultilinearSection 𝕜 F IB E n s) :
    domDomCongr (IB := IB) n e₂ (domDomCongr (IB := IB) n e₁ α)
      = domDomCongr (IB := IB) n (e₁.trans e₂) α  := by sorry

theorem domDomCongr_add {s s' : ℕ} (e : Fin s ≃ Fin s')
    (α β : MultilinearSection 𝕜 F IB E n s) :
    domDomCongr (IB := IB) n e (α + β)
      = domDomCongr (IB := IB) n e α + domDomCongr (IB := IB) n e β  := by sorry

theorem domDomCongr_smul {s s' : ℕ} (e : Fin s ≃ Fin s') (c : 𝕜)
    (α : MultilinearSection 𝕜 F IB E n s) :
    domDomCongr (IB := IB) n e (c • α) = c • domDomCongr (IB := IB) n e α  := by sorry

theorem product_domDomCongr_left {s s' q : ℕ} (e : Fin s ≃ Fin s')
    (α : MultilinearSection 𝕜 F IB E n s) (β : MultilinearSection 𝕜 F IB E n q) :
    product (IB := IB) n (domDomCongr (IB := IB) n e α) β
      = domDomCongr (IB := IB) n
          (finSumFinEquiv.symm.trans
            ((Equiv.sumCongr e (Equiv.refl (Fin q))).trans finSumFinEquiv))
          (product (IB := IB) n α β)  := by sorry

end DifferentialGeometry.MultilinearSection

