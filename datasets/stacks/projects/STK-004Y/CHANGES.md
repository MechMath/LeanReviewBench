# Lean migration

Source: [https://github.com/optpku/stacks at `e2299cf97f975b08e7b5b59202ed00adc80ff6b7`](https://github.com/optpku/stacks/blob/e2299cf97f975b08e7b5b59202ed00adc80ff6b7/ReasLib/Topology/IrreducibleCloseds/Hausdorff.lean).

Roots: `TopologicalSpace.IrreducibleCloseds.exists_eq_singleton`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate local imports and package the selected historical declarations. Keep each selected statement and its definition context, including historical proof admissions.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
