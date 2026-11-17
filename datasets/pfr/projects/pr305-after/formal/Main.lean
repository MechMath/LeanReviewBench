module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Algebra.Group.Pointwise.Finset.BigOperators
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Additive.RuzsaCovering
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Pairwise
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Complement
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Kernel.IndepFun
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.UniformOn
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Finiteness
public import Mathlib.Util.Notation3
public import dep.PFR.Endgame
public import dep.PFR.ForMathlib.ConditionalIndependence
public import dep.PFR.ForMathlib.Entropy.Basic
public import dep.PFR.ForMathlib.Entropy.Kernel.Basic
public import dep.PFR.ForMathlib.Entropy.Kernel.MutualInfo
public import dep.PFR.ForMathlib.Entropy.Kernel.RuzsaDist
public import dep.PFR.ForMathlib.Entropy.Measure
public import dep.PFR.ForMathlib.Entropy.RuzsaDist
public import dep.PFR.ForMathlib.FiniteRange.Defs
public import dep.PFR.ForMathlib.FourVariables
public import dep.PFR.ForMathlib.Pair
public import dep.PFR.ForMathlib.Uniform
public import dep.PFR.Mathlib.MeasureTheory.Constructions.Pi
public import dep.PFR.Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import dep.PFR.Mathlib.MeasureTheory.Measure.Prod
public import dep.PFR.Mathlib.Probability.IdentDistrib
public import dep.PFR.Mathlib.Probability.Independence.Basic
public import dep.PFR.Mathlib.Probability.Kernel.Composition.Comp
public import dep.PFR.Mathlib.Probability.Kernel.Disintegration
public import dep.PFR.MoreRuzsaDist
public import dep.PFR.MultiTauFunctional
public import dep.PFR.Tactic.RPowSimp
public import dep.PFR.TauFunctional

public section

open MeasureTheory ProbabilityTheory Set

open scoped Pointwise

section AnalyzeMinimizer

universe u

variable {G Ωₒ : Type u} [MeasurableFinGroup G] [hΩ₀ : MeasureSpace Ωₒ] {p : multiRefPackage G Ωₒ}
  {Ω : Fin p.m → Type u}
  (hΩ : ∀ i, MeasureSpace (Ω i)) {X : ∀ i, Ω i → G} (h_min : multiTauMinimizes p Ω hΩ X)
  (hΩ_prob : ∀ i, IsProbabilityMeasure (hΩ i).volume) (hX_mes : ∀ i, Measurable (X i))

local notation3 "k" => D[X; hΩ]

variable {Ω' : Type u} {Y : Fin p.m × Fin p.m → Ω' → G}

local notation3 "W" => ∑ i, ∑ j, Y (i, j)

local notation3 "Z1" => ∑ i: Fin p.m, ∑ j, (i:ℤ) • Y (i, j)

local notation3 "Z2" => ∑ i, ∑ j: Fin p.m, (j:ℤ) • Y (i, j)

local notation3 "Z3" => ∑ i: Fin p.m, ∑ j: Fin p.m, (-i-j:ℤ) • Y (i, j)

local notation3 "P" => fun i ↦ ∑ j, Y (i, j)

local notation3 "Q" => fun j ↦ ∑ i, Y (i, j)

local notation3 "R" => fun r ↦ ∑ i, ∑ j, if (i+j+r = 0) then Y r else 0

variable [hΩ' : MeasureSpace Ω'] [hΩ'_prob : IsProbabilityMeasure hΩ'.volume]
  (h_mes : ∀ i j, Measurable (Y (i, j))) (h_indep : iIndepFun Y)
  (hident : ∀ i j, IdentDistrib (Y (i, j)) (X i))

end AnalyzeMinimizer

universe u

open Real

/-- Suppose that $G$ is an abelian group of torsion $m$ (not necessarily finite).
If $A \subset G$ is a finite non-empty set with $|A+A| \leq K|A|$, then $A$ can be covered by at
most $m K^{256 m^3+1}$ translates of a finite subspace $H$ of $G$ with $|H| \leq |A|$. -/
theorem torsion_PFR {G : Type*} [AddCommGroup G] {m : ℕ} (hm : m ≥ 2)
    (htorsion : ∀ x : G, m • x = 0) {A : Set G} (Afin : A.Finite) {K : ℝ} (h₀A : A.Nonempty)
    (hA : Nat.card (A + A) ≤ K * A.ncard) :
    ∃ (H : AddSubgroup G) (c : Set G), c.Finite ∧ (H : Set G).Finite ∧
      Nat.card c < m * K ^ (256 * m ^ 3 + 1) ∧ (H : Set G).ncard ≤ A.ncard ∧ A ⊆ c + H := sorry
