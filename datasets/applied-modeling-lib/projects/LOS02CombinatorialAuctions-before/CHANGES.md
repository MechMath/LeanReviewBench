# Lean migration

Source: [https://github.com/nikhgarg/AppliedModelingLib at `eb67cc832a74734e521fdbe7bb584238ab2ac0a8`](https://github.com/nikhgarg/AppliedModelingLib/blob/eb67cc832a74734e521fdbe7bb584238ab2ac0a8/papers/LOS02CombinatorialAuctions/PaperInterface.lean).

Roots: `LOS02CombinatorialAuctions.PaperInterface.theorem10_2_averageGreedy_truthful`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Cslib `7c8f6c0f67015df29b152fdcffaf7850db2e9185`.

Relocate project-local imports and adapt the historical finite-sum/probability interfaces and proof elaboration. Preserve the selected mechanism, rating-system or fair-division formulation.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

Recorded compatibility edits affect `EconCSLib/Foundations/Math/FiniteSum.lean`, `EconCSLib/MechanismDesign/Auctions/Combinatorial.lean`.
