# Lean migration

Source: [https://github.com/nikhgarg/AppliedModelingLib at `ba9d01206fdb3e5e595efcb501ab5104a345ae36`](https://github.com/nikhgarg/AppliedModelingLib/blob/ba9d01206fdb3e5e595efcb501ab5104a345ae36/papers/GN21DriverSurgePricing/PaperInterface.lean).

Roots: `GN21DriverSurgePricing.PaperInterface.theorem1_single_state_threshold_best_response`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate project-local imports and adapt the historical CTMC/probability interfaces and proof elaboration. Preserve the selected finite-state model, interval/mass parameters and target formulation.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

Recorded compatibility edits affect `EconCSLib/Foundations/Probability/CTMC.lean`, `EconCSLib/Foundations/Probability/MeasureInequalities.lean`, `GN21DriverSurgePricing/MainTheorems.lean`, `GN21DriverSurgePricing/ProofInterface.lean`.
