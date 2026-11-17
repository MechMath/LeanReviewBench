# Lean migration

Source: [https://github.com/teorth/pfr at `3d7898164ebff70a809dce618f9082a7b39e7850`](https://github.com/teorth/pfr/blob/3d7898164ebff70a809dce618f9082a7b39e7850/PFR/EntropyPFR.lean).

Roots: `entropic_PFR_conjecture'`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate imports and retain the selected historical root and definition context.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
