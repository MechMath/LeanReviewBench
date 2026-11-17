# Lean migration

Source: [https://github.com/leanprover-community/add-combi at `2d061f437c1ba00ba9b16d7cba1c7603ba4807a4`](https://github.com/leanprover-community/add-combi/blob/2d061f437c1ba00ba9b16d7cba1c7603ba4807a4/AddCombi/Mathlib/Combinatorics/Additive/Energy.lean).

Roots: `Finset.card_sq_le_card_mul_addEnergy'`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate imports and retain the selected historical root and definition context.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
