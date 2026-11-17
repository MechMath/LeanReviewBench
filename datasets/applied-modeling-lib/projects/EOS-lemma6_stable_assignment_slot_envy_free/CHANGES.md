# Lean migration

Source: [https://github.com/nikhgarg/AppliedModelingLib at `0f8ab772a3432265c5bd3d0b90bb4a8de52aff27`](https://github.com/nikhgarg/AppliedModelingLib/blob/0f8ab772a3432265c5bd3d0b90bb4a8de52aff27/papers/EOS07GSP/PaperInterface.lean).

Roots: `EOS07GSP.PaperInterface.lemma6_stable_assignment_slot_envy_free`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Vendor the target-specific historical EconCSLib auction modules as project-local dependencies. Recover the required auction declarations from AppliedModelingLib commit `3c6a64802de232585064cf906faaefc9ba31b3bc`. Relocate imports and retain the historical target type. Proof/API compatibility changes do not alter the auction definitions or the reviewed target.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
