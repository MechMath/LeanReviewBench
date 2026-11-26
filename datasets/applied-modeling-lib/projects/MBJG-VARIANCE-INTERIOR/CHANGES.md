# Lean migration

Source: [https://github.com/nikhgarg/AppliedModelingLib at `2476b3ff09cca173477757dfe87b31c5884608ee`](https://github.com/nikhgarg/AppliedModelingLib/blob/2476b3ff09cca173477757dfe87b31c5884608ee/papers/MBJG25ProducerFairness/PaperInterface.lean).

Roots: `MBJG25ProducerFairness.paper_facing_theorem3_1_variance_strict_decrease_interior`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate project-local imports and adapt the historical finite-sum/probability interfaces and proof elaboration. Preserve the selected mechanism, rating-system or fair-division formulation.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

## Released statement context

- Retain the target declaration closure and source support needed to elaborate it; remove other declarations and modules.
- Replace theorem and lemma bodies, proof-valued declaration bodies, and proof-valued tactic blocks with `sorry`. Preserve declaration types, section parameters, and computational definitions.
