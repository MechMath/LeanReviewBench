# Lean migration

Source: [https://github.com/nikhgarg/AppliedModelingLib at `25686396b1003e5e5bf44b06a1bf6f0319658660`](https://github.com/nikhgarg/AppliedModelingLib/blob/25686396b1003e5e5bf44b06a1bf6f0319658660/papers/LG21TestOptionalPolicies/PaperInterface.lean).

Roots: `LG21TestOptionalPolicies.paper_interface_theorem3_1_report_required_source_witness_of_base_crossings`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate imports and adapt the historical probability/Gaussian interfaces and proof elaboration. Preserve the selected reporting-policy assumptions and conclusion.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

Recorded compatibility edits affect `EconCSLib/Foundations/Probability/Admissions.lean`, `EconCSLib/Foundations/Probability/Gaussian.lean`, `LG21TestOptionalPolicies/MainTheorems.lean`.
