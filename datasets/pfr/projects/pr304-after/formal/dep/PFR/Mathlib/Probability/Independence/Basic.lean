module

public import Mathlib.Data.Finset.Pairwise
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Kernel.IndepFun

public section

open Function MeasureTheory MeasurableSpace Measure Set

open scoped MeasureTheory ENNReal

namespace ProbabilityTheory

variable {Ω ι β β' γ : Type*} {κ : ι → Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β}
  {g : Ω → β'}

end ProbabilityTheory

namespace ProbabilityTheory

variable {Ω ι β γ : Type*} {κ : ι → Type*}

section IndepFun

variable {β β' γ γ' : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β} {g : Ω → β'}

section iIndepFun

variable {Ω ι ι' : Type*} [MeasurableSpace Ω] {α β : ι → Type*}
  [n : ∀ i, MeasurableSpace (α i)]
  [m : ∀ i, MeasurableSpace (β i)] {f : ∀ i, Ω → α i}
  {μ : Measure Ω}

variable (i : ι) [Inv (α i)] [MeasurableInv (α i)] [DecidableEq ι] in
@[to_additive]
lemma iIndepFun.inv (h : iIndepFun f μ) : iIndepFun (update f i (f i)⁻¹) μ := sorry

universe u

end iIndepFun

variable {Ω' α : Type*} [MeasurableSpace Ω'] [MeasurableSpace α] [MeasurableSpace β]

variable {f : Ω → α} {g : Ω → β}

end IndepFun

end ProbabilityTheory

namespace ProbabilityTheory

variable {ι Ω : Type*} {κ : ι → Type*} {α : ∀ i, κ i → Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [m : ∀ i j, MeasurableSpace (α i j)] {f : ∀ i j, Ω → α i j}

variable [Fintype ι] [∀ i, Fintype (κ i)]

variable {ι : Type*} {κ : ι → Type*} [∀ i, Finite (κ i)]
  {α : ∀ i, κ i → Type*} {f : ∀ i j, Ω → α i j} [m : ∀ i j, MeasurableSpace (α i j)]

/-- If a family of functions `(i, j) ↦ f i j` is independent, then the family of function tuples
`i ↦ (f i j)ⱼ` is independent. -/
lemma iIndepFun.pi
    (f_meas : ∀ i j, Measurable (f i j))
    (hf : iIndepFun (fun ij : Σ i, κ i ↦ f ij.1 ij.2) μ) :
    iIndepFun (fun i ω j ↦ f i j ω) μ := sorry

variable {ι ι' : Type*} {α : ι → Type*}
    {n : (i : ι) → MeasurableSpace (α i)} {f : (i : ι) → Ω → α i}

include n in
lemma iIndepFun.prod {hf : ∀ (i : ι), Measurable (f i)} {ST : ι' → Finset ι}
    (hS : Pairwise (Disjoint on ST)) (h : iIndepFun f μ) :
    let β := fun k ↦ Π i : ST k, α i
    iIndepFun (β := β) (fun (k : ι') (x : Ω) (i : ST k) ↦ f i x) μ := sorry

variable {β β' Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

end ProbabilityTheory
