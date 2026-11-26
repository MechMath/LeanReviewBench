# Lean migration

Source: [https://github.com/nikhgarg/AppliedModelingLib at `ba9d01206fdb3e5e595efcb501ab5104a345ae36`](https://github.com/nikhgarg/AppliedModelingLib/blob/ba9d01206fdb3e5e595efcb501ab5104a345ae36/papers/GN21DriverSurgePricing/PaperInterface.lean).

Roots: `GN21DriverSurgePricing.PaperInterface.theorem3_small_surge_final_sign`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate project-local imports and adapt the historical CTMC/probability interfaces and proof elaboration. Preserve the selected finite-state model, interval/mass parameters and target formulation.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

Before context pruning, compatibility edits affected `EconCSLib/Foundations/Probability/CTMC.lean`, `EconCSLib/Foundations/Probability/MeasureInequalities.lean`, `GN21DriverSurgePricing/MainTheorems.lean`, `GN21DriverSurgePricing/ProofInterface.lean`.

## Released statement context

- Retain the target declaration closure and source support needed to elaborate it; remove other declarations and modules.
- Replace theorem and lemma bodies, proof-valued declaration bodies, and proof-valued tactic blocks with `sorry`. Preserve declaration types, section parameters, and computational definitions.
