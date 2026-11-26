module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.CondDistrib
public import dep.PFR.Mathlib.Probability.Kernel.Disintegration

public section

open Function MeasureTheory Real

open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory.Kernel

section

variable {α β γ δ ε : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    {_ : MeasurableSpace γ} {_ : MeasurableSpace δ} {_ : MeasurableSpace ε}

variable {Ω S T : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace γ]
  {κ : Kernel T S} {μ : Measure T} {X : Ω → S} {Y : Ω → β}

/-- Given a kernel taking values in a product of three spaces, forget the middle one. -/
noncomputable
def deleteMiddle (κ : Kernel α (β × γ × δ)) :
    Kernel α (β × δ) :=
  mapOfMeasurable κ (fun p ↦ (p.1, p.2.2))
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd))

instance (κ : Kernel α (β × γ × δ)) [IsMarkovKernel κ] : IsMarkovKernel (deleteMiddle κ) := sorry

instance (κ : Kernel α (β × γ × δ)) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (deleteMiddle κ) := sorry

/-- Given a kernel taking values in a product of three spaces, forget the last variable. -/
noncomputable
def deleteRight (κ : Kernel α (β × γ × δ)) : Kernel α (β × γ) :=
  mapOfMeasurable κ (fun p ↦ (p.1, p.2.1))
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))

instance (κ : Kernel α (β × γ × δ)) [IsMarkovKernel κ] : IsMarkovKernel (deleteRight κ) := sorry

instance (κ : Kernel α (β × γ × δ)) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (deleteRight κ) := sorry

/-- Given a kernel taking values in a product of three spaces, reverse the order of the spaces. -/
noncomputable
def reverse (κ : Kernel α (β × γ × δ)) : Kernel α (δ × γ × β) :=
  mapOfMeasurable κ (fun p ↦ (p.2.2, p.2.1, p.1))
    ((measurable_snd.comp measurable_snd).prodMk
      ((measurable_fst.comp measurable_snd).prodMk measurable_fst))

instance (κ : Kernel α (β × γ × δ)) [IsMarkovKernel κ] : IsMarkovKernel (reverse κ) := sorry

instance (κ : Kernel α (β × γ × δ)) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (reverse κ) := sorry

end

end ProbabilityTheory.Kernel
