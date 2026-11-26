# Lean migration

Source: [https://github.com/nikhgarg/AppliedModelingLib at `cf500b748ac63dbff55faf97d989d4935c8eff50`](https://github.com/nikhgarg/AppliedModelingLib/blob/cf500b748ac63dbff55faf97d989d4935c8eff50/papers/GCG24UserItemFairness/PaperInterface.lean).

Roots: `GCG24UserItemFairness.PaperInterface.theorem3_price_decreases_first_halfSpec`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Vendor the required historical EconCSLib modules and select the relevant recommendation-model declarations. Adapt finite-sum and finite-optimization APIs, make policy/cardinality unfoldings explicit, and adjust fiber/LP proof elaboration. Preserve the snapshot-specific model definitions and target statement.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

## Released statement context

- Retain the target declaration closure and source support needed to elaborate it; remove other declarations and modules.
- Replace theorem and lemma bodies, proof-valued declaration bodies, and proof-valued tactic blocks with `sorry`. Preserve declaration types, section parameters, and computational definitions.
