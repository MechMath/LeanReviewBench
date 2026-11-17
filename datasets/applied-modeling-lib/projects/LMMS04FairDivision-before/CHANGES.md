# Lean migration

Source: [https://github.com/nikhgarg/AppliedModelingLib at `eb67cc832a74734e521fdbe7bb584238ab2ac0a8`](https://github.com/nikhgarg/AppliedModelingLib/blob/eb67cc832a74734e521fdbe7bb584238ab2ac0a8/papers/LMMS04FairDivision/PaperInterface.lean).

Roots: `LMMS04FairDivision.PaperInterface.theorem2_1_algorithm_correct_list_toFinset`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Cslib `7c8f6c0f67015df29b152fdcffaf7850db2e9185`.

Relocate project-local imports and adapt the historical finite-sum/probability interfaces and proof elaboration. Preserve the selected mechanism, rating-system or fair-division formulation.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

Recorded compatibility edits affect `EconCSLib/Foundations/Probability/RealDistribution.lean`, `LMMS04FairDivision/MainTheorems.lean`, `LMMS04FairDivision/Theorem31QueryLowerBound.lean`, `LMMS04FairDivision/Theorem34BoundedOptimal.lean`.
