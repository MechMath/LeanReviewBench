module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.CondDistrib

@[expose] public section

open Real MeasureTheory Measure ProbabilityTheory

open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory

variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace T] [MeasurableSpace U]

namespace Kernel

section condKernel

variable [Countable U] [Nonempty U] [DiscreteMeasurableSpace U]

variable [Countable T] [MeasurableSingletonClass S] [MeasurableSingletonClass T]

end condKernel

end Kernel

section condDistrib

variable [MeasurableSingletonClass T]

variable [Countable U] [DiscreteMeasurableSpace U]

variable {X : Ω → S} {Y : Ω → T} {Z : Ω → U}

variable [Countable T]

variable [Nonempty T]

section Independence

variable {V : Type*} [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
  {W : Ω → V}

end Independence

end condDistrib

end ProbabilityTheory

open Real MeasureTheory

open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {Ω S T U V : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]

/-- The analogue of FiniteSupport for probability kernels. -/
noncomputable def FiniteKernelSupport (κ : Kernel T S) : Prop :=
  ∀ t, ∃ A : Finset S, κ t Aᶜ = 0

/-- A kernel `κ` has almost everywhere finite support wrt a measure `μ` if, for almost every
point `t`, then `κ t` has finite support. Note that we don't require any uniformity wrt `t`. -/
noncomputable def AEFiniteKernelSupport (κ : Kernel T S) (μ : Measure T) : Prop :=
  ∀ᵐ t ∂μ, ∃ A : Finset S, κ t Aᶜ = 0

section

variable [Countable T] [MeasurableSingletonClass T] {μ : Measure T}

/-- The definition doesn't use `_hκ`, but we keep it here still as it doesn't give anything
interesting otherwise. -/
@[nolint unusedArguments]
noncomputable
def AEFiniteKernelSupport.mk {μ} {κ : Kernel T S} (_hκ : AEFiniteKernelSupport κ μ) :
    Kernel T S := by
  classical
  exact if hS : Nonempty S then
    κ.piecewise (s := {t | ∃ A : Finset S, κ t Aᶜ = 0}) (by rw [Set.ofPred_exists]; measurability)
       (.const _ <| .dirac hS.some)
  else 0

instance AEFiniteKernelSupport.isMarkovKernel_mk
    {κ : Kernel T S} [IsMarkovKernel κ] (hκ : AEFiniteKernelSupport κ μ) :
    IsMarkovKernel hκ.mk := sorry

instance AEFiniteKernelSupport.isZeroOrMarkovKernel_mk
    {κ : Kernel T S} [IsZeroOrMarkovKernel κ] (hκ : AEFiniteKernelSupport κ μ) :
    IsZeroOrMarkovKernel hκ.mk := sorry

instance AEFiniteKernelSupport.isSFiniteKernel_mk
    {κ : Kernel T S} [IsSFiniteKernel κ] (hκ : AEFiniteKernelSupport κ μ) :
    IsSFiniteKernel hκ.mk := sorry

end

/-- maps preserve finite kernel support. -/
lemma FiniteKernelSupport.map [MeasurableSingletonClass U]
    {κ : Kernel T S} (hκ : FiniteKernelSupport κ) (f : S → U) :
    FiniteKernelSupport (map κ f) := sorry

lemma AEFiniteKernelSupport.map [MeasurableSingletonClass U] {κ : Kernel T S} {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) {f : S → U} :
    AEFiniteKernelSupport (Kernel.map κ f) μ := sorry

/-- Projecting a kernel to first coordinate preserves finite kernel support. -/
lemma FiniteKernelSupport.fst [MeasurableSingletonClass S]
   {κ : Kernel T (S × U)} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (fst κ) := sorry

lemma AEFiniteKernelSupport.fst [MeasurableSingletonClass S] {κ : Kernel T (S × U)} {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) :
    AEFiniteKernelSupport (fst κ) μ := sorry

/-- Projecting a kernel to second coordinate preserves finite kernel support. -/
lemma FiniteKernelSupport.snd [MeasurableSingletonClass U]
    {κ : Kernel T (S × U)} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (snd κ) := sorry

lemma AEFiniteKernelSupport.snd [MeasurableSingletonClass U] {κ : Kernel T (S × U)} {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) :
    AEFiniteKernelSupport (snd κ) μ := sorry

/-- Products preserve finite kernel support. -/
lemma FiniteKernelSupport.prod {κ : Kernel T S} {η : Kernel T U}
    [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    [IsMarkovKernel κ] [IsMarkovKernel η]
    (hκ : FiniteKernelSupport κ) (hη : FiniteKernelSupport η) :
    FiniteKernelSupport (κ ×ₖ η) := sorry

lemma AEFiniteKernelSupport.prod {κ : Kernel T S} {η : Kernel T U}
    [IsMarkovKernel κ] [IsMarkovKernel η] {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η μ) :
    AEFiniteKernelSupport (κ ×ₖ η) μ := sorry

end ProbabilityTheory.Kernel
