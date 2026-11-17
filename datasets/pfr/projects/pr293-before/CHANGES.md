# Lean migration

Source: [https://github.com/teorth/pfr at `3a3e20cb71942aefe62ada0dc0b6416645b1b0e8`](https://github.com/teorth/pfr/blob/3a3e20cb71942aefe62ada0dc0b6416645b1b0e8/PFR/ApproxHomPFR.lean).

Roots: `approx_hom_pfr'`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate imports and retain the selected historical root and definition context.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
