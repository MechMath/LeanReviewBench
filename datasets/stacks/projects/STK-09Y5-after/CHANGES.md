# Lean migration

Source: [https://github.com/optpku/stacks at `e420713207f0a6682a65b2171362b77f2d217fa4`](https://github.com/optpku/stacks/blob/e420713207f0a6682a65b2171362b77f2d217fa4/ReasLib/Topology/Stratification/Refinement.lean).

Roots: `LocallyClosedPartition.exists_finite_good_refinement`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate local imports and package the selected historical declarations. Keep each selected statement and its definition context, including historical proof admissions.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

## Released statement context

- Retain the target declaration closure and source support needed to elaborate it; remove other declarations and modules.
- Replace theorem and lemma bodies, proof-valued declaration bodies, and proof-valued tactic blocks with `sorry`. Preserve declaration types, section parameters, and computational definitions.
