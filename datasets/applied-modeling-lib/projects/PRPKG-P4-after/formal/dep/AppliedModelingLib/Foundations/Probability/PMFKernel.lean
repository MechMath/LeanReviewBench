import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace AppliedModelingLib

open MeasureTheory ProbabilityTheory

/-- A discrete stochastic kernel represented directly as a PMF-valued map.
Domain-specific policies and transition rules may use transparent aliases of
this carrier while retaining their own semantic names. -/
abbrev PMFKernel (Input Output : Type*) := Input → PMF Output

namespace PMFKernel

end PMFKernel

/-- Regard a countable PMF-valued transition rule as a measure kernel. -/
noncomputable def pmfToMeasureKernel
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [Countable β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] (transition : PMFKernel α β) : Kernel α β :=
  Kernel.ofFunOfCountable fun input => (transition input).toMeasure

instance pmfToMeasureKernel.isMarkovKernel
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [Countable β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] (transition : PMFKernel α β) :
    IsMarkovKernel (pmfToMeasureKernel transition) := sorry

end AppliedModelingLib
