# Lean migration

Source: [https://github.com/teorth/pfr at `dc2291513cc1020a91fc5024d8f78a17b8c8b746`](https://github.com/teorth/pfr/blob/dc2291513cc1020a91fc5024d8f78a17b8c8b746/PFR/ImprovedPFR.lean).

Roots: `entropic_PFR_conjecture_improv'`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate imports and retain the selected historical root and definition context.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

## Released statement context

- Retain the target declaration closure and source support needed to elaborate it; remove other declarations and modules.
- Replace theorem and lemma bodies, proof-valued declaration bodies, and proof-valued tactic blocks with `sorry`. Preserve declaration types, section parameters, and computational definitions.
