import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import dep.Covering.FiniteSubGaussianChaining

open Set

open scoped BigOperators Interval

namespace FormalSLT.Covering.TotalBoundedDudley

open FormalSLT.Covering.FiniteSubGaussianChaining

noncomputable section

universe u

variable {T : Type u}

/-- A finite net bundled with its finite index type.

`FiniteSubGaussianChaining.FiniteNet` is indexed by an explicit finite type of
centers. Mathlib's total-boundedness API returns finite sets of centers, so this
small bundle carries the finite subtype and the resulting `FiniteNet` together.
-/
structure BundledFiniteNet (T : Type u) where
  A : Type u
  instFintype : Fintype A
  instNonempty : Nonempty A
  net : @FiniteNet T A instFintype

namespace BundledFiniteNet

attribute [instance] instFintype instNonempty

/-- Cardinality of the bundled finite net. -/
def coveringNumber (B : BundledFiniteNet T) : ℕ :=
  @FiniteNet.coveringNumber T B.A B.instFintype B.net

end BundledFiniteNet

/-- Convert an explicit finite metric cover of the whole space into the
finite-net record used by the finite chaining layer. -/
def finiteNetOfCoverSet [PseudoMetricSpace T] [Nonempty T]
    (C : Set T) (hCfinite : C.Finite)
    (r : ℝ) (hr : 0 ≤ r)
    (hcover : ∀ t : T, ∃ c : T, c ∈ C ∧ dist t c ≤ r) :
    BundledFiniteNet T := by
  classical
  let A : Type u := {c : T // c ∈ C}
  let instFintype : Fintype A := hCfinite.fintype
  have instNonempty : Nonempty A := by
    obtain ⟨t⟩ := (inferInstance : Nonempty T)
    obtain ⟨c, hc, _hc_dist⟩ := hcover t
    exact ⟨⟨c, hc⟩⟩
  let project : T → A := fun t =>
    ⟨Classical.choose (hcover t), (Classical.choose_spec (hcover t)).1⟩
  let N : @FiniteNet T A instFintype :=
    { dist := fun s t => dist s t
      dist_nonneg := fun s t => dist_nonneg
      center := fun a => a.1
      project := project
      radius := r
      radius_nonneg := hr
      covers := sorry }
  exact
    { A := A
      instFintype := instFintype
      instNonempty := instNonempty
      net := N }

/-- A totally bounded metric index space admits a finite metric cover at every
positive real radius. This is the Mathlib extraction step, stated with `dist`
and `≤` so it can feed `FiniteNet`. -/
theorem finiteMetricCoverOfTotallyBoundedUniv [PseudoMetricSpace T]
    (hT : TotallyBounded (Set.univ : Set T)) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Set T, C.Finite ∧ ∀ t : T, ∃ c : T, c ∈ C ∧ dist t c ≤ ε := sorry

/-- Extract a bundled finite net from a totally bounded metric index space at
any positive radius. The net uses the ambient metric distance and covers every
point within radius `ε`. -/
def finiteNetOfTotallyBoundedUniv [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) (ε : ℝ) (hε : 0 < ε) :
    BundledFiniteNet T := by
  classical
  let cover := finiteMetricCoverOfTotallyBoundedUniv (T := T) hT hε
  exact finiteNetOfCoverSet
    (Classical.choose cover)
    (Classical.choose_spec cover).1
    ε hε.le
    (Classical.choose_spec cover).2

/-- Radius used for the dyadic finite-net schedule in the first
total-bounded Dudley bridge.

The extra `2^2` shrinkage leaves room for adjacent projection increments:
`r_j + r_{j+1} <= radiusScale / 2^j`. -/
def dyadicChainingNetRadius (radiusScale : ℝ) (j : ℕ) : ℝ :=
  radiusScale / (2 : ℝ) ^ (j + 2)

/-- Positivity of the dyadic net radius under a positive top scale. -/
theorem dyadicChainingNetRadius_pos {radiusScale : ℝ}
    (hradiusScale : 0 < radiusScale) (j : ℕ) :
    0 < dyadicChainingNetRadius radiusScale j := sorry

/-- The dyadic finite-net schedule extracted from total boundedness. -/
def dyadicChainingFiniteNetOfTotallyBoundedUniv
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    BundledFiniteNet T :=
  finiteNetOfTotallyBoundedUniv
    (T := T) hT (dyadicChainingNetRadius radiusScale j)
    (dyadicChainingNetRadius_pos hradiusScale j)

/-- Center type used by the finite terminal dyadic wrapper.

The second component carries the total-bounded dyadic net at scale `j`; the
first component lets the same type support the identity terminal net. -/
def dyadicTerminalNetCenterType
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) : Type u :=
  T × (dyadicChainingFiniteNetOfTotallyBoundedUniv
    (T := T) hT hradiusScale j).A

instance dyadicTerminalNetCenterType.instFintype
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    Fintype (dyadicTerminalNetCenterType (T := T) hT hradiusScale j) := by
  let D := dyadicChainingFiniteNetOfTotallyBoundedUniv
    (T := T) hT hradiusScale j
  letI : Fintype D.A := D.instFintype
  change Fintype (T × D.A)
  infer_instance

instance dyadicTerminalNetCenterType.instNonempty
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    Nonempty (dyadicTerminalNetCenterType (T := T) hT hradiusScale j) := sorry

end

end FormalSLT.Covering.TotalBoundedDudley
