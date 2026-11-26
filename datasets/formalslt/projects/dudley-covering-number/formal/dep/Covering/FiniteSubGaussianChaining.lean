import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace FormalSLT.Covering.FiniteSubGaussianChaining

open Finset

open scoped BigOperators Interval

noncomputable section

variable {Ω T A : Type*}

/-- Weighted expectation over a finite outcome space. The caller supplies the
weights and their probabilistic assumptions separately. -/
def finiteExpectation [Fintype Ω] (p : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  ∑ ω : Ω, p ω * X ω

/-- Supremum over a finite nonempty index type. -/
def finiteSup [Fintype T] [Nonempty T] (f : T → ℝ) : ℝ :=
  (univ : Finset T).sup' univ_nonempty f

/-- A finite ε-net with an explicit nearest-net projection. `A` is the finite
type of net points, `center` realizes a net point in `T`, and `project` chooses
a nearest-net index for each target point. -/
structure FiniteNet (T A : Type*) [Fintype A] where
  dist : T → T → ℝ
  dist_nonneg : ∀ s t : T, 0 ≤ dist s t
  center : A → T
  project : T → A
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  covers : ∀ t : T, dist t (center (project t)) ≤ radius

namespace FiniteNet

/-- The nearest-net projection as a map back into the ambient index type. -/
def projection [Fintype A] (N : FiniteNet T A) : T → T :=
  fun t => N.center (N.project t)

/-- The cardinality of the finite net, i.e. the discrete covering number
represented by this chosen net. -/
def coveringNumber [Fintype A] (_N : FiniteNet T A) : ℕ :=
  Fintype.card A

/-- The finite set of net indices actually hit by the projection map. This is
a finite replacement for taking a supremum over an ambient index type `T`.
It is useful when `T` is not finite but a projected supremum only ranges over
the image of a finite net. -/
def ProjectedIndex [Fintype A] (N : FiniteNet T A) : Type _ :=
  {a : A // ∃ t : T, a = N.project t}

instance projectedIndexFintype [Fintype A] (N : FiniteNet T A) :
    Fintype (ProjectedIndex N) := by
  classical
  unfold ProjectedIndex
  infer_instance

instance projectedIndexNonempty [Fintype A] [Nonempty T] (N : FiniteNet T A) :
    Nonempty (ProjectedIndex N) := sorry

namespace ProjectedIndex

/-- A chosen ambient source point whose projection realizes a projected net
index. The choice is finite-image bookkeeping only; later theorems use it to
build chains without assuming the ambient type is finite. -/
def source [Fintype A] (N : FiniteNet T A) (a : ProjectedIndex N) : T :=
  Classical.choose a.2

end ProjectedIndex

/-- The finite family of projection pairs realized by projecting the same
ambient point into two finite nets. This lets finite chaining pay entropy for
the realized increment family rather than for the full ambient index type. -/
def ProjectionPair [Fintype A] {B : Type*} [Fintype B]
    (N₀ : FiniteNet T A) (N₁ : FiniteNet T B) : Type _ :=
  {ab : A × B // ∃ t : T, ab = (N₀.project t, N₁.project t)}

instance projectionPairFintype
    [Fintype A] {B : Type*} [Fintype B]
    (N₀ : FiniteNet T A) (N₁ : FiniteNet T B) :
    Fintype (ProjectionPair N₀ N₁) := by
  classical
  unfold ProjectionPair
  infer_instance

instance projectionPairNonempty
    [Fintype A] {B : Type*} [Fintype B] [Nonempty T]
    (N₀ : FiniteNet T A) (N₁ : FiniteNet T B) :
    Nonempty (ProjectionPair N₀ N₁) := sorry

end FiniteNet

/-- A finite weighted process with sub-Gaussian increment MGF control.

The process is indexed by a finite type `T` and observed on a finite outcome
space `Ω`. The MGF field is intentionally abstract: later modules can derive it
from concrete Gaussian/Rademacher constructions, while this module only needs a
clean finite-process interface. -/
structure FiniteSubGaussianProcess (Ω T : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  weight_nonneg : ∀ ω : Ω, 0 ≤ weight ω
  weight_sum_one : ∑ ω : Ω, weight ω = 1
  X : Ω → T → ℝ
  dist : T → T → ℝ
  dist_nonneg : ∀ s t : T, 0 ≤ dist s t
  varianceProxy : ℝ
  varianceProxy_nonneg : 0 ≤ varianceProxy
  mgf_increment :
    ∀ s t : T, ∀ lam : ℝ,
      finiteExpectation weight (fun ω => Real.exp (lam * (X ω t - X ω s))) ≤
        Real.exp (lam ^ 2 * varianceProxy * dist s t ^ 2 / 2)

namespace FiniteSubGaussianProcess

end FiniteSubGaussianProcess

namespace FiniteSubGaussianProcess

/-- A reusable finite dyadic net sequence for projected finite-net Dudley
bounds.

The bundle records only finite-scale data: a sequence of finite nets, adjacent
cover-count bounds, a dyadic radius scale, and the metric hypotheses needed by
the chaining theorem. It does not assert total boundedness, separability, or a
continuous entropy integral. -/
structure FiniteDyadicNetSequence
    [Fintype Ω]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)] where
  N : ∀ j : ℕ, FiniteNet T (A j)
  coverCount : ℕ → ℕ
  radiusScale : ℝ
  dist_eq : ∀ j : ℕ, (N j).dist = P.dist
  dist_symm : ∀ s t : T, P.dist s t = P.dist t s
  dist_triangle : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z
  radiusScale_nonneg : 0 ≤ radiusScale
  radius_pos : ∀ j : ℕ, 0 < (N j).radius + (N (j + 1)).radius
  radius_geometric : ∀ j : ℕ,
    (N j).radius + (N (j + 1)).radius ≤ radiusScale / (2 : ℝ) ^ j
  pair_card_gt_one : ∀ j : ℕ,
    1 < Fintype.card (FiniteNet.ProjectionPair (N j) (N (j + 1)))
  coverCount_le : ∀ j : ℕ,
    (N j).coveringNumber * (N (j + 1)).coveringNumber ≤ coverCount j

namespace FiniteDyadicNetSequence

end FiniteDyadicNetSequence

/-- A reusable finite-dyadic Dudley instance for a fixed finite
sub-Gaussian process.

This packages the data that examples otherwise repeat at every use site:
the dyadic net sequence, a coarse expected-supremum budget, positivity of the
variance proxy, and the proof that the terminal projected image at scale `m`
has the stated coarse budget. Supplied suprema are optional and are packaged by
`FiniteDyadicDudleyInstance.SupremumAdapter`.
-/
structure FiniteDyadicDudleyInstance
    [Fintype Ω] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (A : ℕ → Type*) [∀ j, Fintype (A j)] where
  netSequence : FiniteDyadicNetSequence P A
  coarseBudget : ℝ
  variance_pos : 0 < P.varianceProxy
  coarse_bound : ∀ m : ℕ,
    finiteExpectation P.weight
      (fun ω => finiteSup
        (fun u : FiniteNet.ProjectedIndex (netSequence.N m) =>
          P.X ω ((netSequence.N 0).projection
            (FiniteNet.ProjectedIndex.source (netSequence.N m) u)))) ≤
      coarseBudget

namespace FiniteDyadicDudleyInstance

end FiniteDyadicDudleyInstance

end FiniteSubGaussianProcess

end

end FormalSLT.Covering.FiniteSubGaussianChaining
