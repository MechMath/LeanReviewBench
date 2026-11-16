import dep.LegacyMap
import Mathlib.Probability.Notation
import Mathlib.Probability.UniformOn
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open MeasureTheory ProbabilityTheory Real
open scoped Pointwise ENNReal
universe uG
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {G : Type uG} [MeasurableSpace G]
noncomputable def KL_div (X : Ω → G) (Y: Ω' → G) (μ : Measure Ω := by volume_tac)
    (μ' : Measure Ω' := by volume_tac) : ℝ :=
  ∑' x, (PFRHistorical.map X μ {x}).toReal * log ((PFRHistorical.map X μ {x}).toReal / (PFRHistorical.map Y μ' {x}).toReal)


notation3:max "KL[" X " ; " μ " # " Y " ; " μ' "]" => KL_div X Y μ μ'
notation3:max "KL[" X " # " Y "]" => KL_div X Y volume volume
namespace ProbabilityTheory
variable {S : Type*} {Ω : Type*} [MeasurableSpace Ω]
structure IsUniform (H : Set S) (X : Ω → S) (μ : Measure Ω := by volume_tac) : Prop where
  eq_of_mem : ∀ x y, x ∈ H → y ∈ H → μ (X ⁻¹' {x}) = μ (X ⁻¹' {y})
  measure_preimage_compl : μ (X ⁻¹' Hᶜ) = 0


end ProbabilityTheory

variable [AddCommGroup G] [Fintype G]
noncomputable def rho_minus {Ω : Type*} [MeasureSpace Ω]
    (X : Ω → G) (A : Finset G) : ℝ :=
  sInf { x:ℝ | ∃ (Ω':Type uG) (mΩ':MeasureSpace Ω') (T : Ω' → G) (U: Ω' → G), (IsUniform A U) ∧
    (IndepFun T U) ∧ (x = KL[ X # T + U])}

