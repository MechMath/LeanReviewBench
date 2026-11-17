# Lean migration

Source: [https://github.com/teorth/pfr at `e7218bb78ede5124aeac5f9e3beb01190e028af0`](https://github.com/teorth/pfr/blob/e7218bb78ede5124aeac5f9e3beb01190e028af0/PFR/ApproxHomPFR.lean).

Roots: `approx_hom_pfr'`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate imports and retain the selected historical root and definition context.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
