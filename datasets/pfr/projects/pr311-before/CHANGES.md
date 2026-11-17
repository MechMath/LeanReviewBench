# Lean migration

Source: [https://github.com/teorth/pfr at `ce7d2919453ab3a3349700841e76f230740359dd`](https://github.com/teorth/pfr/blob/ce7d2919453ab3a3349700841e76f230740359dd/PFR/ForMathlib/ConditionalIndependence.lean).

Roots: `ProbabilityTheory.condIndep_copies`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate imports and retain the selected historical root and definition context.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

## Released statement context

- Retain the target declaration closure and source support needed to elaborate it; remove other declarations and modules.
- Replace theorem and lemma bodies, proof-valued declaration bodies, and proof-valued tactic blocks with `sorry`. Preserve declaration types, section parameters, and computational definitions.
