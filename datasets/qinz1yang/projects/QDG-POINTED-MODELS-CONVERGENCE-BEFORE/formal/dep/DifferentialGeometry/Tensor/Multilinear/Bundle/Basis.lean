


import dep.DifferentialGeometry.Tensor.Multilinear.Bundle.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace DifferentialGeometry.Tensor.Multilinear


noncomputable section

open _root_.Bundle Set

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

local notation "MLF" s => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜

noncomputable instance multilinearMap_finiteDimensional (s : ℕ) :
    FiniteDimensional 𝕜 (MultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) := by
  have : Module.Finite 𝕜 F := inferInstance
  have : Module.Free 𝕜 F := inferInstance
  have : Module.Finite 𝕜 𝕜 := inferInstance
  have : Module.Free 𝕜 𝕜 := inferInstance
  infer_instance

noncomputable instance continuousMultilinearMap_finiteDimensional (s : ℕ) :
    FiniteDimensional 𝕜 (MLF s) := by
  have : FiniteDimensional 𝕜 (MultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
    multilinearMap_finiteDimensional s
  exact FiniteDimensional.of_injective
    ContinuousMultilinearMap.toMultilinearMapLinear
    ContinuousMultilinearMap.toMultilinearMap_injective

theorem finrank_continuousMultilinearMap (s : ℕ) :
    Module.finrank 𝕜 (MLF s) = (Module.finrank 𝕜 F) ^ s  := by sorry

noncomputable def continuousMultilinearMapBasisElem {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F)
    (s : ℕ) (σ : Fin s → Fin d) : MLF s :=
  (ContinuousMultilinearMap.mkPiRing 𝕜 (Fin s) (1 : 𝕜)).compContinuousLinearMap
    (fun j => LinearMap.toContinuousLinearMap (b.coord (σ j)))

theorem continuousMultilinearMap_basisElem_apply {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F) (s : ℕ)
    (σ σ' : Fin s → Fin d) :
    continuousMultilinearMapBasisElem b s σ (fun j => b (σ' j)) =
    if σ = σ' then 1 else 0  := by sorry

theorem continuousMultilinearMap_basisElem_linearIndependent {d : ℕ}
    (b : Module.Basis (Fin d) 𝕜 F) (s : ℕ) :
    LinearIndependent 𝕜 (continuousMultilinearMapBasisElem b s)  := by sorry

noncomputable def continuousMultilinearMapBasis {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F)
    (s : ℕ) : Module.Basis (Fin s → Fin d) 𝕜 (MLF s) :=
  Module.Basis.mk (continuousMultilinearMap_basisElem_linearIndependent b s)
    ((continuousMultilinearMap_basisElem_linearIndependent b s).span_eq_top_of_card_eq_finrank'
      (by
        have hd : Module.finrank 𝕜 F = d := by
          rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
          finrank_continuousMultilinearMap, hd])).ge

theorem continuousMultilinearMap_basis_repr {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F)
    (s : ℕ) (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) (σ : Fin s → Fin d) :
    (continuousMultilinearMapBasis b s).repr f σ = f (fun j => b (σ j))  := by sorry

section smooth

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  (E : B → Type*) [Π x, AddCommMonoid (E x)] [Π x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [Π x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

omit [ContMDiffVectorBundle n F E IB] in
theorem contMDiff_multilinearSection_iff_coord {d : ℕ}
    (b : Module.Basis (Fin d) 𝕜 F) {s : ℕ}
    (f : ∀ x : B, _root_.Bundle.continuousMultilinearMap 𝕜 s F E x) :
    ContMDiff IB (IB.prod 𝓘(𝕜, MLF s)) n
      (fun x => TotalSpace.mk' (MLF s) x (f x)) ↔
    ∀ σ : Fin s → Fin d, ∀ x₀ : B,
      ContMDiffAt IB 𝓘(𝕜, 𝕜) n
        (fun x => (continuousMultilinearMapBasis b s).repr
          (trivializationAt (MLF s)
            (_root_.Bundle.continuousMultilinearMap 𝕜 s F E) x₀ ⟨x, f x⟩).2 σ) x₀  := by sorry

end smooth

end

end DifferentialGeometry.Tensor.Multilinear

