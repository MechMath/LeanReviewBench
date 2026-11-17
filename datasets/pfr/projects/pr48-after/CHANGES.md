# Lean migration

Source: [https://github.com/teorth/pfr at `52831e9b317ad6daf1bd1046ae3ddfe9f2f80b48`](https://github.com/teorth/pfr/blob/52831e9b317ad6daf1bd1046ae3ddfe9f2f80b48/PFR/ruzsa_distance.lean).

Roots: `ent_of_diff_le`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate imports and retain the selected historical root and definition context.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

## Released statement context

- Retain the target declaration closure and source support needed to elaborate it; remove other declarations and modules.
- Replace theorem and lemma bodies, proof-valued declaration bodies, and proof-valued tactic blocks with `sorry`. Preserve declaration types, section parameters, and computational definitions.
