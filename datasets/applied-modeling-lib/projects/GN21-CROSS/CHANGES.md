# Lean migration

Source: [https://github.com/nikhgarg/AppliedModelingLib at `e1e995e3d6bcf7adc75c0cf5a461cbf90523e48a`](https://github.com/nikhgarg/AppliedModelingLib/blob/e1e995e3d6bcf7adc75c0cf5a461cbf90523e48a/papers/GN21DriverSurgePricing/PaperInterface.lean).

Roots: `GN21DriverSurgePricing.PaperInterface.theorem3_structured_measurable_ic_ae_unique_of_bracket_cross_fields`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate project-local imports and adapt the historical CTMC/probability interfaces and proof elaboration. Preserve the selected finite-state model, interval/mass parameters and target formulation.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

Recorded compatibility edits affect `EconCSLib/Foundations/Probability/CTMC.lean`, `EconCSLib/Foundations/Probability/MeasureInequalities.lean`, `GN21DriverSurgePricing/MainTheorems.lean`, `GN21DriverSurgePricing/PaperInterface.lean`.
