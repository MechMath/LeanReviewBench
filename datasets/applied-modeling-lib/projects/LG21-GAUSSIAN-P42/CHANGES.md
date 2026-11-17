# Lean migration

Source: [https://github.com/nikhgarg/AppliedModelingLib at `aef6c898c5570156989acb6d75fb9b4013997f1e`](https://github.com/nikhgarg/AppliedModelingLib/blob/aef6c898c5570156989acb6d75fb9b4013997f1e/papers/LG21TestOptionalPolicies/PaperInterface.lean).

Roots: `LG21TestOptionalPolicies.paper_interface_proposition4_2_not_law_latent_skill_fair_of_gaussian_mean_gap`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate imports and adapt the historical probability/Gaussian interfaces and proof elaboration. Preserve the selected reporting-policy assumptions and conclusion.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

Recorded compatibility edits affect `EconCSLib/Foundations/Probability/Admissions.lean`, `EconCSLib/Foundations/Probability/Gaussian.lean`, `LG21TestOptionalPolicies/MainTheorems.lean`.
