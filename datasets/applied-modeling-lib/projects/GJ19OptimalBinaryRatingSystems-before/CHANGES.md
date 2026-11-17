# Lean migration

Source: [https://github.com/nikhgarg/AppliedModelingLib at `fa5379e08df8c13e2bbfb85757bd2675b201d124`](https://github.com/nikhgarg/AppliedModelingLib/blob/fa5379e08df8c13e2bbfb85757bd2675b201d124/papers/GJ19OptimalBinaryRatingSystems/PaperInterface.lean).

Roots: `GJ19OptimalBinaryRatingSystems.PaperInterface.theorem31_source_matching_function_unique_value_argmax_lexicographic`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate project-local imports and adapt the historical finite-sum/probability interfaces and proof elaboration. Preserve the selected mechanism, rating-system or fair-division formulation.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

Recorded compatibility edits affect `EconCSLib/Foundations/Math/Asymptotics.lean`, `EconCSLib/Foundations/Math/BinomialBounds.lean`, `EconCSLib/Foundations/Math/EpsilonContinuity.lean`, `EconCSLib/Foundations/Math/FiniteOptimization.lean`, `EconCSLib/Foundations/Math/FiniteSum.lean`, `EconCSLib/Foundations/Probability/BinaryRatingLDP.lean`, `EconCSLib/Foundations/Probability/FiniteEmpiricalMultinomialCounts.lean`, `EconCSLib/Foundations/Probability/FiniteProductMultinomialCounts.lean`, `EconCSLib/Foundations/Probability/FiniteRatingComparison.lean`, `EconCSLib/Foundations/Probability/FiniteSupportMGF.lean`, `EconCSLib/Foundations/Probability/IIDLargeDeviations.lean`, `EconCSLib/Foundations/Probability/LargeDeviations.lean`, `EconCSLib/Foundations/Probability/MeasureInequalities.lean`, `GJ19OptimalBinaryRatingSystems/AppendixB.lean`, `GJ19OptimalBinaryRatingSystems/Assumptions.lean`, `GJ19OptimalBinaryRatingSystems/AuditInterface.lean`, `GJ19OptimalBinaryRatingSystems/ContinuumTheorems.lean`, `GJ19OptimalBinaryRatingSystems/ExperimentTheorems.lean`, `GJ19OptimalBinaryRatingSystems/MainTheorems.lean`, `GJ19OptimalBinaryRatingSystems/PaperInterface.lean`, `GJ19OptimalBinaryRatingSystems/Theorem32Appendix.lean`.
