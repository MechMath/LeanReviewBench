# Lean migration

Source: [https://github.com/nikhgarg/AppliedModelingLib at `fa5379e08df8c13e2bbfb85757bd2675b201d124`](https://github.com/nikhgarg/AppliedModelingLib/blob/fa5379e08df8c13e2bbfb85757bd2675b201d124/papers/GCG24UserItemFairness/PaperInterface.lean).

Roots: `GCG24UserItemFairness.PaperInterface.theorem3_price_decreases_first_half`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Vendor the required historical EconCSLib modules and select the relevant recommendation-model declarations. Adapt finite-sum and finite-optimization APIs, make policy/cardinality unfoldings explicit, and adjust fiber/LP proof elaboration. Preserve the snapshot-specific model definitions and target statement.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
