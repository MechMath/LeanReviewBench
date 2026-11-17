# Lean migration

Source: [https://github.com/nikhgarg/AppliedModelingLib at `3523dfea9e3d6e6fa54db3594fe2b3140a31f18d`](https://github.com/nikhgarg/AppliedModelingLib/blob/3523dfea9e3d6e6fa54db3594fe2b3140a31f18d/papers/LMMS04FairDivision/PaperInterface.lean).

Roots: `LMMS04FairDivision.PaperInterface.theorem2_1_algorithm_correct_list_toFinset`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Cslib `7c8f6c0f67015df29b152fdcffaf7850db2e9185`.

Relocate project-local imports and adapt the historical finite-sum/probability interfaces and proof elaboration. Preserve the selected mechanism, rating-system or fair-division formulation.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

Before context pruning, compatibility edits affected `EconCSLib/Foundations/Probability/RealDistribution.lean`, `LMMS04FairDivision/MainTheorems.lean`, `LMMS04FairDivision/Theorem31QueryLowerBound.lean`, `LMMS04FairDivision/Theorem34BoundedOptimal.lean`.

## Released statement context

- Retain the target declaration closure and source support needed to elaborate it; remove other declarations and modules.
- Replace theorem and lemma bodies, proof-valued declaration bodies, and proof-valued tactic blocks with `sorry`. Preserve declaration types, section parameters, and computational definitions.
