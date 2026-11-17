# Lean migration

Source: [https://github.com/nikhgarg/AppliedModelingLib at `c5fb3adb73dccce16bb7dfe3a0256e8dc387df1e`](https://github.com/nikhgarg/AppliedModelingLib/blob/c5fb3adb73dccce16bb7dfe3a0256e8dc387df1e/papers/LG21TestOptionalPolicies/PaperInterface.lean).

Roots: `LG21TestOptionalPolicies.paper_interface_theorem3_1_optional_reporting_threshold_equilibrium_exists_of_crossing`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate imports and adapt the historical probability/Gaussian interfaces and proof elaboration. Preserve the selected reporting-policy assumptions and conclusion.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

Recorded compatibility edits affect `EconCSLib/Foundations/Probability/Admissions.lean`, `EconCSLib/Foundations/Probability/Gaussian.lean`, `LG21TestOptionalPolicies/MainTheorems.lean`.
