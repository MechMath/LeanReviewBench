module

public import Mathlib.Data.Finset.Pairwise
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
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

/-- If `f` is a family of mutually independent random variables, `(S j)ⱼ` are pairwise disjoint
finite index sets, then the tuples formed by `f i` for `i ∈ S j` are mutually independent,
when seen as a family indexed by `J`. -/
lemma iIndepFun.finsets {f : ∀ i, Ω → β i} {J : Type*} [Finite J]
    (S : J → Finset ι) (h_disjoint : Set.PairwiseDisjoint Set.univ S)
    (hf_Indep : iIndepFun f μ) (hf_meas : ∀ i, Measurable (f i)) :
    iIndepFun (fun (j : J) ↦ fun a (i : S j) ↦ f i a) μ := sorry

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

variable {ι ι' : Type*} {α : ι → Type*}
    {n : (i : ι) → MeasurableSpace (α i)} {f : (i : ι) → Ω → α i}

variable {β β' Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

end ProbabilityTheory
