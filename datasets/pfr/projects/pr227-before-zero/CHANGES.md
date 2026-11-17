# Lean migration

Source: [https://github.com/teorth/pfr at `3dd249a8aec4961bc55de4744643fc3db7b4f252`](https://github.com/teorth/pfr/blob/3dd249a8aec4961bc55de4744643fc3db7b4f252/PFR/Kullback.lean).

Roots: `KL_div_eq_zero_iff_identDistrib`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate imports and retain the selected historical root and definition context.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

## Released statement context

- Retain the target declaration closure and source support needed to elaborate it; remove other declarations and modules.
- Replace theorem and lemma bodies, proof-valued declaration bodies, and proof-valued tactic blocks with `sorry`. Preserve declaration types, section parameters, and computational definitions.
