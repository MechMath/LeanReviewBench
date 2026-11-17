# Lean migration

Source: [https://github.com/teorth/pfr at `ebe97805ab718bec2ca0ab5268f3e4a69ae76b81`](https://github.com/teorth/pfr/blob/ebe97805ab718bec2ca0ab5268f3e4a69ae76b81/PFR/TorsionEndgame.lean).

Roots: `torsion_PFR`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate imports and retain the selected historical root and definition context.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
