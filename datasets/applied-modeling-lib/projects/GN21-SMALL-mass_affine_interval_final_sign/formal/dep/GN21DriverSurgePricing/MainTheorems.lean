import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Set.Disjoint
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import dep.EconCSLib.Foundations.Probability.CTMC

open EconCSLib

open MeasureTheory

open Filter

open scoped Function ProbabilityTheory Topology ENNReal symmDiff

namespace GN21DriverSurgePricing

noncomputable section

/-- Continuous trip length, represented directly as a real number. -/
abbrev TripLength := ℝ

/-- A driver acceptance policy in one world state: the set of accepted trip lengths. -/
abbrev TripPolicy := Set TripLength

/-- Driver pricing/payment as a function of trip length. -/
abbrev PricingFunction := TripLength → ℝ

/--
Finite open-interval approximation of an open trip policy.  This is the same
Step 1 approximation as `GN21FiniteOpenBallApproximation`, stated with
explicit lower and upper endpoints.
-/
structure GN21FiniteOpenIntervalApproximation
    (μ : Measure TripLength) (σ : TripPolicy) (ε : ℝ≥0∞) where
  index : Type
  finite_index : Fintype index
  lower : index → ℝ
  upper : index → ℝ
  lower_lt_upper : ∀ i, lower i < upper i
  interval_subset : ∀ i, Set.Ioo (lower i) (upper i) ⊆ σ
  measure_omitted_lt :
    μ (σ \ ⋃ i : index, Set.Ioo (lower i) (upper i)) < ε

/--
Paper-local finite interval policy domain used by Lemma 5 Step 2.  Unlike
`GN21FiniteOpenIntervalApproximation`, this structure is independent of the
source measure and approximation error, so endpoint-descent arguments can use
it as their finite domain.
-/
structure GN21FiniteIntervalPolicy where
  index : Type
  finite_index : Fintype index
  lower : index → ℝ
  upper : index → ℝ
  lower_lt_upper : ∀ i, lower i < upper i

/-- The trip-policy set represented by a finite interval policy. -/
def GN21FiniteIntervalPolicy.policy
    (P : GN21FiniteIntervalPolicy) : TripPolicy :=
  ⋃ i : P.index, Set.Ioo (P.lower i) (P.upper i)

/--
Finite interval/ray components for Lemma 5 endpoint descent.  Bounded
intervals are the inner-regularity seeds; positive-domain rays and the full
positive domain are needed because the canonical Lemma 5 policies include
accept-all and unbounded tails.
-/
inductive GN21GeneralizedIntervalComponent where
  | bounded (lower upper : ℝ)
  | positiveBounded (lower upper : ℝ)
  | positiveLeftRay (upper : ℝ)
  | positiveRightRay (lower : ℝ)
  | positiveAll

/-- Trip-policy set represented by one generalized interval/ray component. -/
def GN21GeneralizedIntervalComponent.policy :
    GN21GeneralizedIntervalComponent → TripPolicy
  | .bounded lower upper => Set.Ioo lower upper
  | .positiveBounded lower upper =>
      Set.Ioi (0 : ℝ) ∩ Set.Ioi lower ∩ Set.Iio upper
  | .positiveLeftRay upper => Set.Ioi (0 : ℝ) ∩ Set.Iio upper
  | .positiveRightRay lower => Set.Ioi (0 : ℝ) ∩ Set.Ioi lower
  | .positiveAll => Set.Ioi (0 : ℝ)

/--
Finite generalized interval policy domain for Lemma 5.  This is the finite
descent domain that can contain both the bounded approximation seeds and the
unbounded canonical policies reached by endpoint movements.
-/
structure GN21GeneralizedIntervalPolicy where
  index : Type
  finite_index : Fintype index
  component : index → GN21GeneralizedIntervalComponent

/-- The trip-policy set represented by a generalized finite interval policy. -/
def GN21GeneralizedIntervalPolicy.policy
    (P : GN21GeneralizedIntervalPolicy) : TripPolicy :=
  ⋃ i : P.index, (P.component i).policy

/--
Ordered finite generalized interval/ray policy.  The source proof of Lemma 5
talks about the first, second, and third disjoint components; this list domain
records that ordering explicitly and converts back to the unordered finite
generalized-policy domain used by the existing approximation/descent bridge.
-/
structure GN21GeneralizedIntervalListPolicy where
  components : List GN21GeneralizedIntervalComponent

/-- Convert an ordered component list to the finite generalized-policy domain. -/
def GN21GeneralizedIntervalListPolicy.toGeneralizedIntervalPolicy
    (P : GN21GeneralizedIntervalListPolicy) :
    GN21GeneralizedIntervalPolicy where
  index := Fin P.components.length
  finite_index := inferInstance
  component := fun i => P.components.get i

/-- The trip-policy represented by an ordered component list. -/
def GN21GeneralizedIntervalListPolicy.policy
    (P : GN21GeneralizedIntervalListPolicy) : TripPolicy :=
  P.toGeneralizedIntervalPolicy.policy

/-- Embed a bounded finite interval policy in the generalized interval/ray domain. -/
noncomputable def GN21FiniteIntervalPolicy.toGeneralizedIntervalPolicy
    (P : GN21FiniteIntervalPolicy) : GN21GeneralizedIntervalPolicy where
  index := P.index
  finite_index := P.finite_index
  component := fun i =>
    GN21GeneralizedIntervalComponent.bounded (P.lower i) (P.upper i)

/-- The finite interval policy represented by an approximation certificate. -/
def GN21FiniteOpenIntervalApproximation.policy
    {μ : Measure TripLength} {σ : TripPolicy} {ε : ℝ≥0∞}
    (A : GN21FiniteOpenIntervalApproximation μ σ ε) : TripPolicy :=
  ⋃ i : A.index, Set.Ioo (A.lower i) (A.upper i)

/-- Lifetime earnings-rate functional for a one-state policy. -/
abbrev SingleStateReward := TripPolicy → ℝ

/-- Lifetime earnings-rate functional for a dynamic two-state policy. -/
abbrev DynamicReward := (Fin 2 → TripPolicy) → ℝ

/-- The source domain of positive trip lengths. -/
def positiveTripLengths : TripPolicy :=
  {τ | 0 < τ}

/-- A one-state policy accepts all feasible positive-length trip requests. -/
def acceptsAllTrips (σ : TripPolicy) : Prop :=
  positiveTripLengths ⊆ σ

/-- The accept-all one-state policy. -/
def acceptAllPolicy : TripPolicy :=
  positiveTripLengths

/-- Probability mass of a trip-length acceptance set under the trip distribution. -/
def singleStateTripMass (μ : Measure TripLength) (σ : TripPolicy) : ℝ :=
  (μ σ).toReal

/-- Expected trip time contributed by an accepted trip-length set. -/
def singleStateTripTime (μ : Measure TripLength) (σ : TripPolicy) : ℝ :=
  ∫ τ in σ, τ ∂μ

/-- Expected payment contributed by an accepted trip-length set. -/
def singleStateTripPayment
    (μ : Measure TripLength) (w : PricingFunction) (σ : TripPolicy) : ℝ :=
  ∫ τ in σ, w τ ∂μ

/-- Policy that rejects sufficiently long trips, `σ = (0,t)`. -/
def rejectsLongTrips (t : ℝ) (σ : TripPolicy) : Prop :=
  ∀ ⦃τ : TripLength⦄, 0 < τ → (τ ∈ σ ↔ τ < t)

/-- Policy that rejects sufficiently short trips, `σ = (t,∞)`. -/
def rejectsShortTrips (t : ℝ) (σ : TripPolicy) : Prop :=
  ∀ ⦃τ : TripLength⦄, 0 < τ → (τ ∈ σ ↔ t < τ)

/-- Policy that accepts an interval of medium-length trips, `σ = (lo,hi)`. -/
def acceptsMiddleTrips (lo hi : ℝ) (σ : TripPolicy) : Prop :=
  ∀ ⦃τ : TripLength⦄, 0 < τ → (τ ∈ σ ↔ lo < τ ∧ τ < hi)

/-- Policy that rejects medium-length trips, `σ = (0,lo) ∪ (hi,∞)`. -/
def rejectsMiddleTrips (lo hi : ℝ) (σ : TripPolicy) : Prop :=
  ∀ ⦃τ : TripLength⦄, 0 < τ → (τ ∈ σ ↔ τ < lo ∨ hi < τ)

/-- Dynamic two-state accept-all policy. -/
def acceptAllDynamicPolicy : Fin 2 → TripPolicy :=
  fun _ => acceptAllPolicy

/-- A dynamic policy is optimal for a two-state lifetime reward functional. -/
def dynamicOptimal (R : DynamicReward) (σ : Fin 2 → TripPolicy) : Prop :=
  ∀ ρ : Fin 2 → TripPolicy, R ρ ≤ R σ

/-- Dynamic policies in the source feasible measurable domain. -/
def dynamicFeasibleMeasurablePolicy (σ : Fin 2 → TripPolicy) : Prop :=
  ∀ i : Fin 2, σ i ⊆ acceptAllPolicy ∧ MeasurableSet (σ i)

/--
Feasible measurable dynamic policies with positive accepted trip mass in every
state.  This is the nondegenerate source domain for the measured Lemma 1
decomposition, whose displayed state reward rates divide by `F_i(σ_i)`.
-/
def dynamicFeasibleMeasurablePositiveMassPolicy
    (μ : Fin 2 → Measure TripLength) (σ : Fin 2 → TripPolicy) : Prop :=
  dynamicFeasibleMeasurablePolicy σ ∧
    ∀ i : Fin 2, 0 < singleStateTripMass (μ i) (σ i)

/--
Dynamic optimality restricted to the source feasible measurable policy domain.
The target policy is included in the domain explicitly.
-/
def dynamicMeasurableOptimal
    (R : DynamicReward) (σ : Fin 2 → TripPolicy) : Prop :=
  dynamicFeasibleMeasurablePolicy σ ∧
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicFeasibleMeasurablePolicy ρ → R ρ ≤ R σ

/--
Dynamic measurable IC predicate: accepting all trips in both states is optimal
among feasible measurable dynamic policies.
-/
def dynamicMeasurableIncentiveCompatible (R : DynamicReward) : Prop :=
  dynamicMeasurableOptimal R acceptAllDynamicPolicy

attribute [local simp] dynamicMeasurableIncentiveCompatible

/--
Dynamic optimality restricted to feasible measurable policies whose accepted
trip mass is positive in both states.
-/
def dynamicPositiveMassMeasurableOptimal
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward) (σ : Fin 2 → TripPolicy) : Prop :=
  dynamicFeasibleMeasurablePositiveMassPolicy μ σ ∧
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicFeasibleMeasurablePositiveMassPolicy μ ρ → R ρ ≤ R σ

/--
Dynamic measurable IC on the nondegenerate positive-mass source domain.
-/
def dynamicPositiveMassMeasurableIncentiveCompatible
    (μ : Fin 2 → Measure TripLength) (R : DynamicReward) : Prop :=
  dynamicPositiveMassMeasurableOptimal μ R acceptAllDynamicPolicy

/--
Statewise continuation reward induced by a dynamic reward functional after
holding the other state's policy fixed.
-/
def dynamicStateReward
    (R : DynamicReward) (σ : Fin 2 → TripPolicy) (i : Fin 2) :
    SingleStateReward :=
  fun τ => R (Function.update σ i τ)

/--
A dynamically optimal policy is locally optimal in each state when the other
state's policy is fixed.
-/
theorem dynamicStateReward_optimal_of_dynamicOptimal
    (R : DynamicReward) {σ : Fin 2 → TripPolicy}
    (hσ : dynamicOptimal R σ) (i : Fin 2) :
    ∀ τ : TripPolicy,
      dynamicStateReward R σ i τ ≤ dynamicStateReward R σ i (σ i) := sorry

/--
Section 4.1 two-state CTMC transition probability from state `i` to the other
state after elapsed time `s`.
-/
def gn21SwitchProb (lambdaIJ lambdaJI s : ℝ) : ℝ :=
  twoStateCtmcSwitchProb lambdaIJ lambdaJI s

/-- Lemma 1/3 one-state cycle time `T_i(σ_i)` from the source paper. -/
def gn21StateCycleTime
    (μ : Measure TripLength) (arrivalRate : ℝ) (σ : TripPolicy) : ℝ :=
  1 / (arrivalRate * singleStateTripMass μ σ) +
    singleStateTripTime μ σ / singleStateTripMass μ σ

/-- Lemma 3 integral exit weight `Q_i(σ_i)`. -/
def gn21ExitWeightIntegral
    (μ : Measure TripLength) (arrivalRate switchIJ switchJI : ℝ)
    (σ : TripPolicy) : ℝ :=
  switchIJ + arrivalRate * ∫ τ in σ, gn21SwitchProb switchIJ switchJI τ ∂μ

/--
Appendix D scaled state time `T_i = λ_i F_i(σ_i)T_i(σ_i) =
1 + λ_i ∫_σ τ dF_i(τ)`.
-/
def gn21ScaledStateTime
    (μ : Measure TripLength) (arrivalRate : ℝ) (σ : TripPolicy) : ℝ :=
  1 + arrivalRate * singleStateTripTime μ σ

/-- Structured IC price family from Theorem 3: `w_i(τ)=m_i τ + z_i q_{i→j}(τ)`. -/
def structuredSurgePrice (m z : ℝ) (q : TripLength → ℝ) : PricingFunction :=
  fun τ => m * τ + z * q τ

/-- Theorem 3 structured price using the Lemma 2 two-state CTMC switch probability. -/
def ctmcStructuredSurgePrice
    (m z lambdaIJ lambdaJI : ℝ) : PricingFunction :=
  structuredSurgePrice m z (gn21SwitchProb lambdaIJ lambdaJI)

attribute [local simp] ctmcStructuredSurgePrice

/--
Theorem 3 state-indexed CTMC switch probabilities.  State `0` is the
non-surge state and state `1` is the surge state.
-/
def ctmcDynamicSwitchProb
    (switch12 switch21 : ℝ) (i : Fin 2) : TripLength → ℝ :=
  if i = 0 then
    gn21SwitchProb switch12 switch21
  else
    gn21SwitchProb switch21 switch12

/-- Theorem 3 state-indexed structured CTMC price family. -/
def ctmcStructuredDynamicSurgePrice
    (m z : Fin 2 → ℝ) (switch12 switch21 : ℝ) :
    Fin 2 → PricingFunction :=
  fun i => structuredSurgePrice (m i) (z i)
    (ctmcDynamicSwitchProb switch12 switch21 i)

/--
Lemma 6 scaled derivative-sign kernel:
`q(W_j T_i - T_j W_i) + w_i(u)(Q_i T_j + Q_j T_i)
 - u(Q_i W_j + Q_j W_i)`.
-/
def gn21DerivativeSignKernel
    (q u wi Qi Qj Ti Tj Wi Wj : ℝ) : ℝ :=
  q * (Wj * Ti - Tj * Wi) +
    wi * (Qi * Tj + Qj * Ti) -
      u * (Qi * Wj + Qj * Wi)

/--
Lemma 6 aggregate dynamic reward after Lemma 1's time-fraction reduction:
`(Q_i W_j + Q_j W_i)/(Q_i T_j + Q_j T_i)`.
-/
def gn21AggregateDynamicReward
    (Qi Qj Ti Tj Wi Wj : ℝ) : ℝ :=
  (Qi * Wj + Qj * Wi) / (Qi * Tj + Qj * Ti)

/-- Endpoint path for `Q_i = lambda_{i→j} + lambda_i ∫ q_{i→j}(τ) f_i(τ)dτ`. -/
def gn21EndpointQiPath
    (arrivalRate switchRate lowerEndpoint : ℝ)
    (density switchProb : ℝ → ℝ) (x : ℝ) : ℝ :=
  switchRate +
    arrivalRate * ∫ τ in lowerEndpoint..x, switchProb τ * density τ

/-- Endpoint path for `W_i = lambda_i ∫ w_i(τ) f_i(τ)dτ`. -/
def gn21EndpointWiPath
    (arrivalRate lowerEndpoint : ℝ)
    (density payment : ℝ → ℝ) (x : ℝ) : ℝ :=
  arrivalRate * ∫ τ in lowerEndpoint..x, payment τ * density τ

/-- Endpoint path for `T_i = 1 + lambda_i ∫ τ f_i(τ)dτ`. -/
def gn21EndpointTiPath
    (arrivalRate lowerEndpoint : ℝ)
    (density : ℝ → ℝ) (x : ℝ) : ℝ :=
  1 + arrivalRate * ∫ τ in lowerEndpoint..x, τ * density τ

/-- Two real quantities have the same strict sign. -/
def sameStrictSign (x y : ℝ) : Prop :=
  (0 < x ↔ 0 < y) ∧ (x < 0 ↔ y < 0)

/--
Lemma 6 source-facing endpoint: the analytic derivative has the same sign as
the algebraic derivative kernel.  The hard input is the endpoint-derivative
certificate for the set-valued reward functional.
-/
structure Lemma6DerivativeFormulaCertificate where
  derivativeValue : ℝ
  q : ℝ
  u : ℝ
  wi : ℝ
  Qi : ℝ
  Qj : ℝ
  Ti : ℝ
  Tj : ℝ
  Wi : ℝ
  Wj : ℝ
  same_sign :
    sameStrictSign derivativeValue
      (gn21DerivativeSignKernel q u wi Qi Qj Ti Tj Wi Wj)

/--
Lean-native endpoint derivative data behind Lemma 6.  The continuous
measure-theoretic work is now isolated to:

* a one-dimensional endpoint path `rewardAlongEndpoint`;
* a `HasDerivAt` proof at the endpoint `u`;
* a positive-scale equality between that derivative and Lemma 6's algebraic
  kernel.
-/
structure Lemma6EndpointDerivativeData where
  rewardAlongEndpoint : ℝ → ℝ
  derivativeValue : ℝ
  q : ℝ
  u : ℝ
  wi : ℝ
  Qi : ℝ
  Qj : ℝ
  Ti : ℝ
  Tj : ℝ
  Wi : ℝ
  Wj : ℝ
  scale : ℝ
  scale_pos : 0 < scale
  has_derivative : HasDerivAt rewardAlongEndpoint derivativeValue u
  derivative_eq_scaled_kernel :
    derivativeValue =
      scale * gn21DerivativeSignKernel q u wi Qi Qj Ti Tj Wi Wj

/--
Endpoint derivative data produce the Lemma 6 strict-sign certificate whenever
the derivative is a positive scalar multiple of the algebraic kernel.
-/
def lemma6DerivativeFormulaCertificate_of_endpoint_data
    (D : Lemma6EndpointDerivativeData) :
    Lemma6DerivativeFormulaCertificate where
  derivativeValue := D.derivativeValue
  q := D.q
  u := D.u
  wi := D.wi
  Qi := D.Qi
  Qj := D.Qj
  Ti := D.Ti
  Tj := D.Tj
  Wi := D.Wi
  Wj := D.Wj
  same_sign := sorry

attribute [local simp] lemma6DerivativeFormulaCertificate_of_endpoint_data

/--
Concrete Lemma 6 endpoint-data constructor from the aggregate quotient
calculus.  The remaining measure-theoretic source obligations are exactly the
three endpoint path derivatives for `Q_i`, `W_i`, and `T_i`.
-/
def lemma6EndpointDerivativeData_of_aggregate_paths
    (QiPath WiPath TiPath : ℝ → ℝ)
    (q u wi Qi Qj Ti Tj Wi Wj endpointScale : ℝ)
    (hendpointScale_pos : 0 < endpointScale)
    (hQj_pos : 0 < Qj)
    (hQi_deriv : HasDerivAt QiPath (endpointScale * q) u)
    (hWi_deriv : HasDerivAt WiPath (endpointScale * wi) u)
    (hTi_deriv : HasDerivAt TiPath (endpointScale * u) u)
    (hQi_val : QiPath u = Qi)
    (hWi_val : WiPath u = Wi)
    (hTi_val : TiPath u = Ti)
    (hden : Qi * Tj + Qj * Ti ≠ 0) :
    Lemma6EndpointDerivativeData where
  rewardAlongEndpoint := fun x =>
    gn21AggregateDynamicReward (QiPath x) Qj (TiPath x) Tj (WiPath x) Wj
  derivativeValue :=
    endpointScale * Qj *
      gn21DerivativeSignKernel q u wi Qi Qj Ti Tj Wi Wj /
        (Qi * Tj + Qj * Ti) ^ 2
  q := q
  u := u
  wi := wi
  Qi := Qi
  Qj := Qj
  Ti := Ti
  Tj := Tj
  Wi := Wi
  Wj := Wj
  scale := endpointScale * Qj / (Qi * Tj + Qj * Ti) ^ 2
  scale_pos := sorry
  has_derivative := sorry
  derivative_eq_scaled_kernel := sorry

attribute [local simp] lemma6EndpointDerivativeData_of_aggregate_paths

/--
Density/interval specialization of the Lemma 6 endpoint bridge.  This matches
the source assumptions where the distribution has density `f_i`, and an upper
endpoint `u` moves in an interval with fixed lower endpoint.
-/
def lemma6EndpointDerivativeData_of_interval_density_paths
    (arrivalRate switchRate lowerEndpoint u Qj Tj Wj : ℝ)
    (density switchProb payment : ℝ → ℝ)
    (harrival_pos : 0 < arrivalRate)
    (hdensity_pos : 0 < density u)
    (hQj_pos : 0 < Qj)
    (hden :
      gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density
          switchProb u * Tj +
        Qj *
          gn21EndpointTiPath arrivalRate lowerEndpoint density u ≠ 0)
    (hq_int :
      IntervalIntegrable (fun τ => switchProb τ * density τ) volume
        lowerEndpoint u)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => switchProb τ * density τ) (𝓝 u))
    (hq_cont : ContinuousAt (fun τ => switchProb τ * density τ) u)
    (hw_int :
      IntervalIntegrable (fun τ => payment τ * density τ) volume
        lowerEndpoint u)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => payment τ * density τ) (𝓝 u))
    (hw_cont : ContinuousAt (fun τ => payment τ * density τ) u)
    (ht_int :
      IntervalIntegrable (fun τ => τ * density τ) volume lowerEndpoint u)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) u) :
    Lemma6EndpointDerivativeData :=
  lemma6EndpointDerivativeData_of_aggregate_paths
    (gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density switchProb)
    (gn21EndpointWiPath arrivalRate lowerEndpoint density payment)
    (gn21EndpointTiPath arrivalRate lowerEndpoint density)
    (switchProb u) u (payment u)
    (gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density
      switchProb u)
    Qj
    (gn21EndpointTiPath arrivalRate lowerEndpoint density u)
    Tj
    (gn21EndpointWiPath arrivalRate lowerEndpoint density payment u)
    Wj
    (arrivalRate * density u)
    (mul_pos harrival_pos hdensity_pos)
    hQj_pos
    (sorry)
    (sorry)
    (sorry)
    rfl rfl rfl hden

attribute [local simp] lemma6EndpointDerivativeData_of_interval_density_paths

/-- Strict quasi-convexity on positive trip lengths. -/
def strictQuasiConvexOnPositive (f : TripLength → ℝ) : Prop :=
  ∀ x y θ : ℝ, 0 < x → 0 < y → x ≠ y → 0 < θ → θ < 1 →
    f (θ * x + (1 - θ) * y) < max (f x) (f y)

/-- Strict quasi-concavity on positive trip lengths. -/
def strictQuasiConcaveOnPositive (f : TripLength → ℝ) : Prop :=
  ∀ x y θ : ℝ, 0 < x → 0 < y → x ≠ y → 0 < θ → θ < 1 →
    min (f x) (f y) < f (θ * x + (1 - θ) * y)

/-- Lemma 5 derivative-shape cases and their policy forms. -/
inductive Lemma5DerivativeShape where
  | positive
  | strictlyIncreasing
  | strictlyDecreasing
  | strictlyQuasiConvex
  | strictlyQuasiConcave
  deriving DecidableEq

/-- The policy form produced by Lemma 5 for each derivative-shape case. -/
def lemma5PolicyForm (shape : Lemma5DerivativeShape) (σ : TripPolicy) : Prop :=
  match shape with
  | .positive => acceptsAllTrips σ
  | .strictlyIncreasing => ∃ t : ℝ, rejectsShortTrips t σ
  | .strictlyDecreasing => ∃ t : ℝ, rejectsLongTrips t σ
  | .strictlyQuasiConvex => ∃ lo hi : ℝ, rejectsMiddleTrips lo hi σ
  | .strictlyQuasiConcave => ∃ lo hi : ℝ, acceptsMiddleTrips lo hi σ

/-- Accept-all has Lemma 5's positive-derivative policy form. -/
theorem lemma5PolicyForm_positive_acceptAllPolicy :
    lemma5PolicyForm .positive acceptAllPolicy := sorry

/--
Policy that accepts exactly the positive trip lengths whose marginal response
is strictly positive.  This is the source proof's local-improvement target in
Lemma 5 after the derivative sign has been reduced to a response function.
-/
def lemma5PositiveResponsePolicy (response : TripLength → ℝ) : TripPolicy :=
  {τ | 0 < τ ∧ 0 < response τ}

/-- Linearized marginal reward of a policy for a fixed response function. -/
def lemma5MarginalSetReward
    (μ : Measure TripLength) (response : TripLength → ℝ)
    (σ : TripPolicy) : ℝ :=
  ∫ τ in σ, response τ ∂μ

/--
For the linearized marginal reward associated with a fixed response, the policy
that accepts exactly positive-response trips weakly dominates every measurable
feasible policy.
-/
theorem lemma5MarginalSetReward_le_positiveResponsePolicy
    (μ : Measure TripLength) (response : TripLength → ℝ)
    (σ : TripPolicy)
    (hresponse_measurable : Measurable response)
    (hresponse_integrable_acceptAll :
      IntegrableOn response acceptAllPolicy μ)
    (hσ_measurable : MeasurableSet σ)
    (hσ_subset : σ ⊆ acceptAllPolicy) :
    lemma5MarginalSetReward μ response σ ≤
      lemma5MarginalSetReward μ response
        (lemma5PositiveResponsePolicy response) := sorry

/-- A positive marginal response produces the accept-all Lemma 5 form. -/
theorem lemma5PolicyForm_positiveResponse_positive
    (response : TripLength → ℝ)
    (hpositive : ∀ τ : TripLength, 0 < τ → 0 < response τ) :
    lemma5PolicyForm .positive (lemma5PositiveResponsePolicy response) := sorry

/--
Paper Lemma 5's five response-shape cases, specialized to the
positive-response variational policy.  Each constructor contains the analytic
shape/boundary facts needed to identify `{τ > 0 | 0 < response τ}` with the
corresponding canonical Lemma 5 policy form.
-/
inductive Lemma5PositiveResponseShapeData
    (response : TripLength → ℝ) : Lemma5DerivativeShape → Prop where
  | positive
      (hpositive : ∀ τ : TripLength, 0 < τ → 0 < response τ) :
      Lemma5PositiveResponseShapeData response .positive
  | strictlyIncreasing
      (t : ℝ)
      (ht_pos : 0 < t)
      (hmono : StrictMonoOn response (Set.Ioi 0))
      (hzero : response t = 0) :
      Lemma5PositiveResponseShapeData response .strictlyIncreasing
  | strictlyDecreasing
      (t : ℝ)
      (ht_pos : 0 < t)
      (hanti : StrictAntiOn response (Set.Ioi 0))
      (hzero : response t = 0) :
      Lemma5PositiveResponseShapeData response .strictlyDecreasing
  | strictlyQuasiConvex
      (lo hi : ℝ)
      (hlo_pos : 0 < lo)
      (hlo_hi : lo < hi)
      (hqc : strictQuasiConvexOnPositive response)
      (hlo_zero : response lo = 0)
      (hhi_zero : response hi = 0)
      (hleft_pos :
        ∀ τ : TripLength, 0 < τ → τ < lo → 0 < response τ)
      (hright_pos :
        ∀ τ : TripLength, hi < τ → 0 < response τ) :
      Lemma5PositiveResponseShapeData response .strictlyQuasiConvex
  | strictlyQuasiConcave
      (lo hi : ℝ)
      (hlo_pos : 0 < lo)
      (hlo_hi : lo < hi)
      (hqc : strictQuasiConcaveOnPositive response)
      (hlo_zero : response lo = 0)
      (hhi_zero : response hi = 0)
      (hleft_nonpos :
        ∀ τ : TripLength, 0 < τ → τ < lo → response τ ≤ 0)
      (hright_nonpos :
        ∀ τ : TripLength, hi < τ → response τ ≤ 0) :
      Lemma5PositiveResponseShapeData response .strictlyQuasiConcave

/--
For every response-shape case used in Lemma 5, the positive feasible zero set
of the response is null under a nonatomic trip-length measure.  This is the
measure-theoretic boundary bridge that the source proof leaves implicit when it
uses strict interval forms at derivative zero crossings.
-/
theorem Lemma5PositiveResponseShapeData.positive_zero_set_null
    {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
    (D : Lemma5PositiveResponseShapeData response shape)
    (μ : Measure TripLength) [NullSingletonClass μ] :
    μ ({τ : TripLength | 0 < τ ∧ response τ = 0}) = 0 := sorry

/--
Minimal fixed-response shape data for Lemma 5 after the positive-response
policy has already been identified.  This separates the set-shape and null
boundary obligations from stronger analytic monotonicity/quasi-convexity facts.
-/
structure Lemma5PositiveResponsePolicyFormData
    (response : TripLength → ℝ) (shape : Lemma5DerivativeShape) : Prop where
  policy_form :
    lemma5PolicyForm shape (lemma5PositiveResponsePolicy response)
  positive_zero_set_null :
    ∀ (μ : Measure TripLength) [NullSingletonClass μ],
      μ ({τ : TripLength | 0 < τ ∧ response τ = 0}) = 0

/--
Pointwise positivity is the source proof's simplest Lemma 5 branch: the
positive-response policy is accept-all and there is no positive trip length
with zero response.
-/
def Lemma5PositiveResponsePolicyFormData.positive
    (response : TripLength → ℝ)
    (hpositive : ∀ τ : TripLength, 0 < τ → 0 < response τ) :
    Lemma5PositiveResponsePolicyFormData response .positive where
  policy_form := lemma5PolicyForm_positiveResponse_positive response hpositive
  positive_zero_set_null := sorry

/--
Lemma 5 certificate: a derivative-shape hypothesis lets one replace an open
measurable policy by a policy of the corresponding interval form without
decreasing reward.
-/
structure Lemma5OptimizerReplacementCertificate
    (Rhat : SingleStateReward) (σ0 : TripPolicy)
    (shape : Lemma5DerivativeShape) where
  policy : TripPolicy
  policy_form : lemma5PolicyForm shape policy
  reward_ge : Rhat σ0 ≤ Rhat policy
  strict_unless_initial_form : ¬ lemma5PolicyForm shape σ0 → Rhat σ0 < Rhat policy

/--
Feasible generalized interval/ray policies.  This is the source-faithful
finite seed domain for Lemma 5: interval/ray codes are only used for policies
contained in the positive feasible-trip domain.
-/
structure GN21FeasibleGeneralizedIntervalPolicy where
  toGeneralized : GN21GeneralizedIntervalPolicy
  subset_acceptAll : toGeneralized.policy ⊆ acceptAllPolicy

/-- The trip-policy represented by a feasible generalized interval/ray code. -/
def GN21FeasibleGeneralizedIntervalPolicy.policy
    (P : GN21FeasibleGeneralizedIntervalPolicy) : TripPolicy :=
  P.toGeneralized.policy

/--
If a policy is already optimal for the single-state continuation problem, a
Lemma 5 replacement certificate forces the original policy itself to have the
corresponding Lemma 5 form. Otherwise the strict replacement would contradict
optimality.
-/
theorem lemma5PolicyForm_of_optimizer_replacement_certificate_of_optimal
    (Rhat : SingleStateReward) (σ0 : TripPolicy)
    (shape : Lemma5DerivativeShape)
    (C : Lemma5OptimizerReplacementCertificate Rhat σ0 shape)
    (hoptimal : ∀ σ : TripPolicy, Rhat σ ≤ Rhat σ0) :
    lemma5PolicyForm shape σ0 := sorry

/--
Fixed-response Lemma 5 replacement certificate.  Once the positive-response
policy has the required shape, and every non-shaped current policy either
omits positive-response mass or accepts genuinely negative-response mass, the
linearized marginal reward satisfies the full weak/strict replacement
interface used by later Theorem 4 code.
-/
def lemma5MarginalOptimizerReplacementCertificate_positiveResponse
    (μ : Measure TripLength) (response : TripLength → ℝ)
    (σ0 : TripPolicy) (shape : Lemma5DerivativeShape)
    (hresponse_measurable : Measurable response)
    (hresponse_integrable_acceptAll :
      IntegrableOn response acceptAllPolicy μ)
    (hσ0_measurable : MeasurableSet σ0)
    (hσ0_subset : σ0 ⊆ acceptAllPolicy)
    (hpositive_form :
      lemma5PolicyForm shape (lemma5PositiveResponsePolicy response))
    (hstrict_mass :
      ¬ lemma5PolicyForm shape σ0 →
        0 < μ (lemma5PositiveResponsePolicy response \ σ0) ∨
        0 <
          μ (Function.support response ∩
            (σ0 \ lemma5PositiveResponsePolicy response))) :
    Lemma5OptimizerReplacementCertificate
      (lemma5MarginalSetReward μ response) σ0 shape where
  policy := lemma5PositiveResponsePolicy response
  policy_form := hpositive_form
  reward_ge :=
    lemma5MarginalSetReward_le_positiveResponsePolicy
      μ response σ0 hresponse_measurable hresponse_integrable_acceptAll
      hσ0_measurable hσ0_subset
  strict_unless_initial_form := sorry

attribute [local simp] lemma5MarginalOptimizerReplacementCertificate_positiveResponse

/-- Lemma 9 lower-bound numerator for the structured-price ratio. -/
def lemma9StructuredLowerNumerator
    (T1 Q1 Tbar2 Qbar2 switch21 : ℝ) : ℝ :=
  T1 * (switch21 * Tbar2 - Qbar2) - (Q1 + T1 * switch21)

/-- Lemma 9 lower-bound denominator for the structured-price ratio. -/
def lemma9StructuredLowerDenominator
    (T1 Q1 Tbar2 Qbar2 switch21 : ℝ) : ℝ :=
  Q1 * (switch21 * Tbar2 - Qbar2) +
    switch21 * (Q1 + T1 * switch21)

/-- Lemma 9 upper-bound numerator for the structured-price ratio. -/
def lemma9StructuredUpperNumerator
    (T1 Q1 Qbar2 : ℝ) : ℝ :=
  Qbar2 * T1 + Q1

/-- Lemma 9 upper-bound denominator for the structured-price ratio. -/
def lemma9StructuredUpperDenominator
    (Q1 Qbar2 switch21 : ℝ) : ℝ :=
  Q1 * (Qbar2 - switch21)

/-- Lemma 9 lower bound for the structured-price ratio. -/
def lemma9StructuredLower
    (T1 Q1 Tbar2 Qbar2 switch21 : ℝ) : ℝ :=
  lemma9StructuredLowerNumerator T1 Q1 Tbar2 Qbar2 switch21 /
    lemma9StructuredLowerDenominator T1 Q1 Tbar2 Qbar2 switch21

/-- Lemma 9 upper bound for the structured-price ratio. -/
def lemma9StructuredUpper
    (T1 Q1 _Tbar2 Qbar2 switch21 : ℝ) : ℝ :=
  lemma9StructuredUpperNumerator T1 Q1 Qbar2 /
    lemma9StructuredUpperDenominator Q1 Qbar2 switch21

/-- Lemma 9 structured-price bounds for the surge-state derivative condition. -/
def lemma9StructuredBounds
    (ratio T1 Q1 Tbar2 Qbar2 switch21 : ℝ) : Prop :=
  lemma9StructuredLower T1 Q1 Tbar2 Qbar2 switch21 < ratio ∧
    ratio < lemma9StructuredUpper T1 Q1 Tbar2 Qbar2 switch21

/-- Lemma 10 positive numerator appearing in the lower bound. -/
def lemma10StructuredLowerNumerator
    (T2 Q2 switch12 : ℝ) : ℝ :=
  T2 * switch12 + Q2

/-- Lemma 10 denominator appearing in the lower bound. -/
def lemma10StructuredLowerDenominator
    (T2 Q2 Tbar1 Qbar1 switch12 : ℝ) : ℝ :=
  Q2 * (switch12 * Tbar1 - Qbar1) +
    switch12 * (T2 * switch12 + Q2)

/-- Lemma 10 upper-bound denominator. -/
def lemma10StructuredUpperDenominator
    (Qbar1 switch12 : ℝ) : ℝ :=
  Qbar1 - switch12

/-- Lemma 10 lower bound for the structured-price ratio. -/
def lemma10StructuredLower
    (T2 Q2 Tbar1 Qbar1 switch12 : ℝ) : ℝ :=
  -(lemma10StructuredLowerNumerator T2 Q2 switch12 /
      lemma10StructuredLowerDenominator T2 Q2 Tbar1 Qbar1 switch12)

/-- Lemma 10 upper bound for the structured-price ratio. -/
def lemma10StructuredUpper
    (_T2 _Q2 _Tbar1 Qbar1 switch12 : ℝ) : ℝ :=
  1 / lemma10StructuredUpperDenominator Qbar1 switch12

/-- Lemma 10 structured-price bounds for the non-surge-state derivative condition. -/
def lemma10StructuredBounds
    (ratio T2 Q2 Tbar1 Qbar1 switch12 : ℝ) : Prop :=
  lemma10StructuredLower T2 Q2 Tbar1 Qbar1 switch12 < ratio ∧
    ratio < lemma10StructuredUpper T2 Q2 Tbar1 Qbar1 switch12

/-- Lemma 5 derivative-shape outcomes admissible for Theorem 4 non-surge states. -/
def theorem4NonsurgeAllowedLemma5Shape : Lemma5DerivativeShape → Prop
  | .positive => True
  | .strictlyIncreasing => False
  | .strictlyDecreasing => True
  | .strictlyQuasiConvex => False
  | .strictlyQuasiConcave => True

/-- Lemma 5 derivative-shape outcomes admissible for Theorem 4 surge states. -/
def theorem4SurgeAllowedLemma5Shape : Lemma5DerivativeShape → Prop
  | .positive => True
  | .strictlyIncreasing => True
  | .strictlyDecreasing => False
  | .strictlyQuasiConvex => True
  | .strictlyQuasiConcave => False

/-- The accept-all Lemma 5 case is allowed in non-surge states. -/
theorem theorem4NonsurgeAllowedLemma5Shape_positive :
    theorem4NonsurgeAllowedLemma5Shape .positive := sorry

/-- The accept-all Lemma 5 case is allowed in surge states. -/
theorem theorem4SurgeAllowedLemma5Shape_positive :
    theorem4SurgeAllowedLemma5Shape .positive := sorry

/--
Theorem 4 shape-derivation certificate: a closer interface to the proof chain
from Lemma 5. It records Lemma 5 forms for the exhibited optimum and for every
other optimum, plus the allowed-shape side conditions supplied by Lemmas 7-10.
-/
structure Theorem4ShapeDerivationCertificate (R : DynamicReward) where
  policy : Fin 2 → TripPolicy
  optimal : dynamicOptimal R policy
  nonsurge_shape : Lemma5DerivativeShape
  surge_shape : Lemma5DerivativeShape
  nonsurge_allowed : theorem4NonsurgeAllowedLemma5Shape nonsurge_shape
  surge_allowed : theorem4SurgeAllowedLemma5Shape surge_shape
  nonsurge_form : lemma5PolicyForm nonsurge_shape (policy 0)
  surge_form : lemma5PolicyForm surge_shape (policy 1)
  only_policy_forms :
    ∀ ρ : Fin 2 → TripPolicy, dynamicOptimal R ρ →
      (∃ shape : Lemma5DerivativeShape,
        theorem4NonsurgeAllowedLemma5Shape shape ∧
          lemma5PolicyForm shape (ρ 0)) ∧
      (∃ shape : Lemma5DerivativeShape,
        theorem4SurgeAllowedLemma5Shape shape ∧
          lemma5PolicyForm shape (ρ 1))

/--
Theorem 4 shape-replacement certificate: the analytic Lemma 5 step supplies
strict replacement certificates for the local continuation problem in each
state. Since the policies under consideration are dynamic optima, local
optimality converts those replacement certificates into the Lemma 5 policy
forms required by `Theorem4ShapeDerivationCertificate`.
-/
structure Theorem4ShapeReplacementDerivationCertificate
    (R : DynamicReward) where
  policy : Fin 2 → TripPolicy
  optimal : dynamicOptimal R policy
  nonsurge_shape : Lemma5DerivativeShape
  surge_shape : Lemma5DerivativeShape
  nonsurge_allowed : theorem4NonsurgeAllowedLemma5Shape nonsurge_shape
  surge_allowed : theorem4SurgeAllowedLemma5Shape surge_shape
  nonsurge_replacement :
    Lemma5OptimizerReplacementCertificate
      (dynamicStateReward R policy 0) (policy 0) nonsurge_shape
  surge_replacement :
    Lemma5OptimizerReplacementCertificate
      (dynamicStateReward R policy 1) (policy 1) surge_shape
  only_replacements :
    ∀ ρ : Fin 2 → TripPolicy, dynamicOptimal R ρ →
      (Σ shape :
        {shape : Lemma5DerivativeShape //
          theorem4NonsurgeAllowedLemma5Shape shape},
          Lemma5OptimizerReplacementCertificate
            (dynamicStateReward R ρ 0) (ρ 0) shape.1) ×
      (Σ shape :
        {shape : Lemma5DerivativeShape //
          theorem4SurgeAllowedLemma5Shape shape},
          Lemma5OptimizerReplacementCertificate
            (dynamicStateReward R ρ 1) (ρ 1) shape.1)

/--
Convert Lemma 5 replacement data into the shape-derivation certificate by
applying local optimality of dynamic optima state by state.
-/
def theorem4ShapeDerivationCertificate_of_shape_replacement
    (R : DynamicReward)
    (C : Theorem4ShapeReplacementDerivationCertificate R) :
    Theorem4ShapeDerivationCertificate R where
  policy := C.policy
  optimal := C.optimal
  nonsurge_shape := C.nonsurge_shape
  surge_shape := C.surge_shape
  nonsurge_allowed := C.nonsurge_allowed
  surge_allowed := C.surge_allowed
  nonsurge_form :=
    lemma5PolicyForm_of_optimizer_replacement_certificate_of_optimal
      (dynamicStateReward R C.policy 0) (C.policy 0) C.nonsurge_shape
      C.nonsurge_replacement
      (dynamicStateReward_optimal_of_dynamicOptimal R C.optimal 0)
  surge_form :=
    lemma5PolicyForm_of_optimizer_replacement_certificate_of_optimal
      (dynamicStateReward R C.policy 1) (C.policy 1) C.surge_shape
      C.surge_replacement
      (dynamicStateReward_optimal_of_dynamicOptimal R C.optimal 1)
  only_policy_forms := sorry

attribute [local simp] theorem4ShapeDerivationCertificate_of_shape_replacement

/--
Theorem 4 accept-all derivation certificate: the Lemma 9/10 positive
derivative cases make every optimal policy positive-form in both states, and
the feasible domain excludes non-positive trips.
-/
structure Theorem4AcceptAllDerivationCertificate (R : DynamicReward) where
  accept_all_optimal : dynamicOptimal R acceptAllDynamicPolicy
  feasible_optimal :
    ∀ ρ : Fin 2 → TripPolicy, dynamicOptimal R ρ →
      ∀ i : Fin 2, ρ i ⊆ acceptAllPolicy
  nonsurge_positive_form :
    ∀ ρ : Fin 2 → TripPolicy, dynamicOptimal R ρ →
      lemma5PolicyForm .positive (ρ 0)
  surge_positive_form :
    ∀ ρ : Fin 2 → TripPolicy, dynamicOptimal R ρ →
      lemma5PolicyForm .positive (ρ 1)

/--
The accept-all derivation is a special case of the Theorem 4 shape-derivation
interface with positive Lemma 5 forms in both states.
-/
def theorem4ShapeDerivationCertificate_of_accept_all_derivation
    (R : DynamicReward)
    (C : Theorem4AcceptAllDerivationCertificate R) :
    Theorem4ShapeDerivationCertificate R where
  policy := acceptAllDynamicPolicy
  optimal := C.accept_all_optimal
  nonsurge_shape := .positive
  surge_shape := .positive
  nonsurge_allowed := theorem4NonsurgeAllowedLemma5Shape_positive
  surge_allowed := theorem4SurgeAllowedLemma5Shape_positive
  nonsurge_form := lemma5PolicyForm_positive_acceptAllPolicy
  surge_form := lemma5PolicyForm_positive_acceptAllPolicy
  only_policy_forms := sorry

attribute [local simp] theorem4ShapeDerivationCertificate_of_accept_all_derivation

/-- Lemma 3 displayed time-fraction formula for state `i`. -/
def gn21TimeFractionFormula
    (arrivalI acceptI timeI exitWeightJ
      arrivalJ acceptJ timeJ exitWeightI : ℝ) : ℝ :=
  arrivalI * acceptI * timeI * exitWeightJ /
    (arrivalJ * acceptJ * timeJ * exitWeightI +
      arrivalI * acceptI * timeI * exitWeightJ)

/-- Lemma 3 displayed time-fraction formula using the paper's measured `T_i` and `Q_i`. -/
def gn21MeasuredTimeFraction
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (σI σJ : TripPolicy) : ℝ :=
  gn21TimeFractionFormula
    arrivalI (singleStateTripMass μI σI)
    (gn21StateCycleTime μI arrivalI σI)
    (gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ)
    arrivalJ (singleStateTripMass μJ σJ)
    (gn21StateCycleTime μJ arrivalJ σJ)
    (gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI)

/-- Paper one-state reward rate `W_i / T_i`. -/
def gn21StateRewardRate (meanEarning stateCycleTime : ℝ) : ℝ :=
  meanEarning / stateCycleTime

/-- Lemma 1 mean earning per accepted trip, `W_i(σ_i)`. -/
def gn21StateMeanEarning
    (μ : Measure TripLength) (w : PricingFunction) (σ : TripPolicy) : ℝ :=
  singleStateTripPayment μ w σ / singleStateTripMass μ σ

/-- Lemma 1 measured state reward rate `R_i(w_i,σ_i)=W_i(σ_i)/T_i(σ_i)`. -/
def gn21MeasuredStateRewardRate
    (μ : Measure TripLength) (arrivalRate : ℝ)
    (w : PricingFunction) (σ : TripPolicy) : ℝ :=
  gn21StateRewardRate
    (gn21StateMeanEarning μ w σ)
    (gn21StateCycleTime μ arrivalRate σ)

/-- Lemma 1 dynamic reward decomposition from time fractions and state reward rates. -/
def gn21DynamicRewardFormula
    (timeFractionI rewardRateI timeFractionJ rewardRateJ : ℝ) : ℝ :=
  timeFractionI * rewardRateI + timeFractionJ * rewardRateJ

/--
Lemma 1 measured dynamic reward formula with the paper's measured time
fractions and one-state reward rates.
-/
def gn21MeasuredDynamicReward
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction) (σI σJ : TripPolicy) : ℝ :=
  gn21DynamicRewardFormula
    (gn21MeasuredTimeFraction μI μJ arrivalI arrivalJ switchIJ switchJI σI σJ)
    (gn21MeasuredStateRewardRate μI arrivalI wI σI)
    (gn21MeasuredTimeFraction μJ μI arrivalJ arrivalI switchJI switchIJ σJ σI)
    (gn21MeasuredStateRewardRate μJ arrivalJ wJ σJ)

/--
Dynamic-reward wrapper for the measured two-state CTMC reward formula.  State
`0` is the non-surge state and state `1` is the surge state.
-/
def gn21MeasuredDynamicRewardFunctional
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction) : DynamicReward :=
  fun σ =>
    gn21MeasuredDynamicReward (μ 0) (μ 1) (arrival 0) (arrival 1)
      switch12 switch21 (w 0) (w 1) (σ 0) (σ 1)

/-- Measured dynamic reward specialized to the CTMC structured price family. -/
def gn21MeasuredCTMCStructuredDynamicReward
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (m z : Fin 2 → ℝ) : DynamicReward :=
  gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
    (ctmcStructuredDynamicSurgePrice m z switch12 switch21)

/-- Accept-all scaled state time, used in the measured Theorem 3 endpoint. -/
def gn21AcceptAllScaledStateTime
    (μ : Measure TripLength) (arrivalRate : ℝ) : ℝ :=
  gn21ScaledStateTime μ arrivalRate acceptAllPolicy

/-- Accept-all exit weight, used in the measured Theorem 3 endpoint. -/
def gn21AcceptAllExitWeightIntegral
    (μ : Measure TripLength) (arrivalRate switchIJ switchJI : ℝ) : ℝ :=
  gn21ExitWeightIntegral μ arrivalRate switchIJ switchJI acceptAllPolicy

/-- Theorem 3 feasibility-threshold numerator in the source constant `C`. -/
def theorem3FeasibilityNumerator
    (T1 T2 Q1 Q2 switch12 : ℝ) : ℝ :=
  Q2 * (switch12 * T1 - Q1) + Q1 * (T2 * switch12 + Q2)

/-- Theorem 3 feasibility-threshold denominator before the outer `T1` scaling. -/
def theorem3FeasibilityDenominator
    (T1 T2 Q1 Q2 switch12 : ℝ) : ℝ :=
  Q2 * (switch12 * T1 - Q1) + switch12 * (T2 * switch12 + Q2)

/--
Theorem 3 source threshold
`C = 1 - numerator / (T1 * denominator)`.
-/
def theorem3FeasibilityThresholdC
    (T1 T2 Q1 Q2 switch12 : ℝ) : ℝ :=
  1 -
    theorem3FeasibilityNumerator T1 T2 Q1 Q2 switch12 /
      (T1 * theorem3FeasibilityDenominator T1 T2 Q1 Q2 switch12)

/--
Theorem 3 non-surge structured-price ratio.  If `rho = R_1/R_2` and
`m_1 = R_2`, the state-1 accounting identity
`R_1*T_1 = R_2*(T_1-1)+z_1*(Q_1-lambda)` gives this value of `z_1/R_2`.
-/
def theorem3NonsurgeZRatio
    (rho T1 Q1 switch12 : ℝ) : ℝ :=
  (rho * T1 - (T1 - 1)) / (Q1 - switch12)

/--
Theorem 3 surge multiplier chosen from a feasible Lemma 9 ratio and a target
surge reward rate.
-/
def theorem3SurgeMultiplierFromRatio
    (R1 R2 T2 Q2 switch21 ratio : ℝ) : ℝ :=
  (R2 * T2 + ratio * R1 * (Q2 - switch21)) /
    ((T2 - 1) + ratio * (Q2 - switch21))

/-- The corresponding surge additive coefficient `z_2`. -/
def theorem3SurgeZFromRatio
    (R1 R2 T2 Q2 switch21 ratio : ℝ) : ℝ :=
  ratio *
    (theorem3SurgeMultiplierFromRatio R1 R2 T2 Q2 switch21 ratio - R1)

/--
The parameter identities produced by the Theorem 3 construction once
`T_i,Q_i` are specialized to accept-all measured primitives.  This is the
source-facing evidence that the constructed `m,z` prices have the paper's
closed-form accounting and Lemma 9/10 ratio bounds.
-/
def theorem3AcceptAllStructuredParameterEvidence
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (m z : Fin 2 → ℝ) : Prop :=
  ∃ nonsurgeRatio surgeRatio : ℝ,
    lemma10StructuredBounds nonsurgeRatio
      (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
      (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
      (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
      (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
      switch12 ∧
    lemma9StructuredBounds surgeRatio
      (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
      (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
      (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
      (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
      switch21 ∧
    m 0 = R2 ∧
    z 0 = nonsurgeRatio * R2 ∧
    m 1 =
      theorem3SurgeMultiplierFromRatio R1 R2
        (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
        (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
        switch21 surgeRatio ∧
    z 1 =
      theorem3SurgeZFromRatio R1 R2
        (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
        (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
        switch21 surgeRatio ∧
    m 0 *
        (gn21AcceptAllScaledStateTime (μ 0) (arrival 0) - 1) +
      z 0 *
        (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 -
          switch12) =
        R1 * gn21AcceptAllScaledStateTime (μ 0) (arrival 0) ∧
    m 1 *
        (gn21AcceptAllScaledStateTime (μ 1) (arrival 1) - 1) +
      z 1 *
        (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 -
          switch21) =
        R2 * gn21AcceptAllScaledStateTime (μ 1) (arrival 1)

/--
Positive version of the Theorem 3 accept-all parameter evidence.  The scalar
construction proves the surge ratio is positive; this package preserves that
fact for endpoint routes that need `m_2 > R_1`.
-/
def theorem3AcceptAllStructuredPositiveParameterEvidence
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (m z : Fin 2 → ℝ) : Prop :=
  ∃ nonsurgeRatio surgeRatio : ℝ,
    0 < surgeRatio ∧
    lemma10StructuredBounds nonsurgeRatio
      (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
      (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
      (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
      (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
      switch12 ∧
    lemma9StructuredBounds surgeRatio
      (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
      (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
      (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
      (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
      switch21 ∧
    m 0 = R2 ∧
    z 0 = nonsurgeRatio * R2 ∧
    m 1 =
      theorem3SurgeMultiplierFromRatio R1 R2
        (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
        (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
        switch21 surgeRatio ∧
    z 1 =
      theorem3SurgeZFromRatio R1 R2
        (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
        (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
        switch21 surgeRatio ∧
    m 0 *
        (gn21AcceptAllScaledStateTime (μ 0) (arrival 0) - 1) +
      z 0 *
        (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 -
          switch12) =
        R1 * gn21AcceptAllScaledStateTime (μ 0) (arrival 0) ∧
    m 1 *
        (gn21AcceptAllScaledStateTime (μ 1) (arrival 1) - 1) +
      z 1 *
        (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 -
          switch21) =
        R2 * gn21AcceptAllScaledStateTime (μ 1) (arrival 1)

/--
Readable nondegenerate source-domain conclusion of the measured Theorem 3
endpoint: the constructed structured CTMC prices are IC among feasible
measurable policies with positive accepted trip mass in both states.
-/
def theorem3MeasuredStructuredPositiveMassMeasurableICConclusion
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ) : Prop :=
  ∃ m z : Fin 2 → ℝ,
    (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) ∧
      dynamicPositiveMassMeasurableIncentiveCompatible μ
        (gn21MeasuredCTMCStructuredDynamicReward
          μ arrival switch12 switch21 m z) ∧
      (∃ q : Fin 2 → TripLength → ℝ,
        ∀ i τ,
          ctmcStructuredDynamicSurgePrice m z switch12 switch21 i τ =
            structuredSurgePrice (m i) (z i) (q i) τ) ∧
      theorem3AcceptAllStructuredParameterEvidence
        μ arrival R1 R2 switch12 switch21 m z

/--
Mass-affine small-surge selected-price interval assumptions with the
accept-all Lemma 9 lower endpoint derived from the paper's final-sign
certificate.
-/
structure Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeMassAffineCurrentIntervalSlackFinalSignDataAssumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ) where
  Rmax : ℝ
  hR1_eq : R1 = rho * R2
  hR1_pos : 0 < R1
  hR1_lt_R2 : R1 < R2
  hR2_pos : 0 < R2
  hC_lt_rho :
    theorem3FeasibilityThresholdC
        (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
        (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
        (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
        (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
        switch12 < rho
  hrho_lt_one : rho < 1
  harrival1_pos : 0 < arrival 0
  harrival2_pos : 0 < arrival 1
  hswitch12_pos : 0 < switch12
  hswitch21_pos : 0 < switch21
  htime1_integrable :
    IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0)
  htime2_integrable :
    IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1)
  hq1_integrable :
    IntegrableOn
      (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
      acceptAllPolicy (μ 0)
  hq2_integrable :
    IntegrableOn
      (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
      acceptAllPolicy (μ 1)
  hmass1_pos : 0 < singleStateTripMass (μ 0) acceptAllPolicy
  hmass2_pos : 0 < singleStateTripMass (μ 1) acceptAllPolicy
  hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1
  hfinite1_acceptAll : (μ 0) acceptAllPolicy ≠ ⊤
  Rmax_envelope :
    (theorem3NonsurgeZRatio rho
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          switch12 * R2 ≤ 0 ∧
        Rmax = R2) ∨
      (0 ≤
          theorem3NonsurgeZRatio rho
            (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
            (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
            switch12 * R2 ∧
        Rmax =
          max R2
            ((arrival 0) *
              (theorem3NonsurgeZRatio rho
                (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
                (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
                  switch12 switch21)
                switch12 * R2)))
  Rmax_zero_ratio_pos :
    0 <
      R2 * gn21AcceptAllScaledStateTime (μ 1) (arrival 1) -
        Rmax * (gn21AcceptAllScaledStateTime (μ 1) (arrival 1) - 1)
  acceptAll_lower_left_nonpos :
    lemma9StructuredLowerNumerator
        (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
        (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
          switch12 switch21)
        (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
        (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1)
          switch21 switch12)
        switch21 *
      lemma9StructuredUpperDenominator
        (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
          switch12 switch21)
        (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1)
          switch21 switch12)
        switch21 ≤ 0
  current_lower_interval_slack :
    ∀ m z : Fin 2 → ℝ,
      (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
        theorem3AcceptAllStructuredPositiveParameterEvidence
          μ arrival R1 R2 switch12 switch21 m z →
        ((z 0 ≤ 0 ∧ Rmax = m 0) ∨
          (0 ≤ z 0 ∧ Rmax = max (m 0) ((arrival 0) * z 0))) →
        0 < m 1 - Rmax →
        z 1 <
          ((gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1)
                switch21 switch12 +
              switch12) /
            (switch12 *
              (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1)
                switch21 switch12 - switch21))) *
            (m 1 - Rmax) →
        ∀ policy : Fin 2 → TripPolicy,
          dynamicFeasibleMeasurablePositiveMassPolicy μ policy →
            lemma9StructuredLower
                (gn21ScaledStateTime (μ 0) (arrival 0) (policy 0))
                (gn21ExitWeightIntegral (μ 0) (arrival 0)
                  switch12 switch21 (policy 0))
                (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
                (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1)
                  switch21 switch12)
                switch21 *
              (m 1 -
                gn21MeasuredStateRewardRate (μ 0) (arrival 0)
                  (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
                  (policy 0)) < z 1

end

end GN21DriverSurgePricing
