# Lean migration

Source: [https://github.com/nikhgarg/AppliedModelingLib at `3523dfea9e3d6e6fa54db3594fe2b3140a31f18d`](https://github.com/nikhgarg/AppliedModelingLib/blob/3523dfea9e3d6e6fa54db3594fe2b3140a31f18d/papers/LOS02CombinatorialAuctions/PaperInterface.lean).

Roots: `LOS02CombinatorialAuctions.PaperInterface.theorem10_2_averageGreedy_truthful`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Cslib `7c8f6c0f67015df29b152fdcffaf7850db2e9185`.

Relocate project-local imports and adapt the historical finite-sum/probability interfaces and proof elaboration. Preserve the selected mechanism, rating-system or fair-division formulation.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

Recorded compatibility edits affect `EconCSLib/Foundations/Math/FiniteSum.lean`, `EconCSLib/MechanismDesign/Auctions/Combinatorial.lean`.
