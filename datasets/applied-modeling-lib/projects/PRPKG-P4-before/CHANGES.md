# Lean migration

Source: [https://github.com/nikhgarg/AppliedModelingLib at `e298529dc9f3a48e74afb4b64f4bcde1b85faa46`](https://github.com/nikhgarg/AppliedModelingLib/blob/e298529dc9f3a48e74afb4b64f4bcde1b85faa46/papers/PRPKG24AccuracyDiversity/PaperInterface.lean).

Roots: `PRPKG24AccuracyDiversity.PaperInterface.proposition4`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate project-local imports and adapt the historical finite-sum/probability interfaces and proof elaboration. Preserve the selected mechanism, rating-system or fair-division formulation.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

Before context pruning, compatibility edits affected `AppliedModelingLib/Applications/RatingSystems/BinaryLargeDeviations.lean`, `AppliedModelingLib/Applications/RatingSystems/FiniteComparison.lean`, `AppliedModelingLib/Applications/RecommenderSystems/Allocation.lean`, `AppliedModelingLib/Foundations/Math/AbsolutelyContinuous.lean`, `AppliedModelingLib/Foundations/Math/Asymptotics.lean`, `AppliedModelingLib/Foundations/Math/BinomialBounds.lean`, `AppliedModelingLib/Foundations/Math/EpsilonContinuity.lean`, `AppliedModelingLib/Foundations/Math/ExponentialBounds.lean`, `AppliedModelingLib/Foundations/Math/FiniteOptimization.lean`, `AppliedModelingLib/Foundations/Math/FiniteSum.lean`, `AppliedModelingLib/Foundations/Math/PowerComparisons.lean`, `AppliedModelingLib/Foundations/Probability/Exponential.lean`, `AppliedModelingLib/Foundations/Probability/FiniteEmpiricalMultinomialCounts.lean`, `AppliedModelingLib/Foundations/Probability/FiniteExpectation.lean`, `AppliedModelingLib/Foundations/Probability/FiniteProductMultinomialCounts.lean`, `AppliedModelingLib/Foundations/Probability/FiniteSupportMGF.lean`, `AppliedModelingLib/Foundations/Probability/IIDLargeDeviations.lean`, `AppliedModelingLib/Foundations/Probability/LargeDeviations.lean`, `AppliedModelingLib/Foundations/Probability/OrderStatistics.lean`, `AppliedModelingLib/Foundations/Probability/Pareto.lean`, `AppliedModelingLib/Foundations/Probability/RealDistribution.lean`, `PRPKG24AccuracyDiversity/AppendixD1GenericII.lean`, `PRPKG24AccuracyDiversity/AppendixD1GenericIV.lean`, `PRPKG24AccuracyDiversity/AppendixD2DensitySource.lean`, `PRPKG24AccuracyDiversity/AppendixD3Source.lean`, `PRPKG24AccuracyDiversity/Bounded.lean`, `PRPKG24AccuracyDiversity/ContinuousSphereConcrete.lean`, `PRPKG24AccuracyDiversity/DecayingBernoulli.lean`, `PRPKG24AccuracyDiversity/Examples.lean`, `PRPKG24AccuracyDiversity/ExponentialTopOne.lean`, `PRPKG24AccuracyDiversity/MainTheorems.lean`, `PRPKG24AccuracyDiversity/Pareto.lean`, `PRPKG24AccuracyDiversity/SeparableAsymptotic.lean`, `PRPKG24AccuracyDiversity/TailHomogeneity.lean`, `PRPKG24AccuracyDiversity/Theorem1PmfSource.lean`, `PRPKG24AccuracyDiversity/Theorem2RankBernoulliSource.lean`, `PRPKG24AccuracyDiversity/Uniform.lean`.

## Released statement context

- Retain the target declaration closure and source support needed to elaborate it; remove other declarations and modules.
- Replace theorem and lemma bodies, proof-valued declaration bodies, and proof-valued tactic blocks with `sorry`. Preserve declaration types, section parameters, and computational definitions.
