# Lean migration

Source: [https://github.com/RemyDegenne/brownian-motion at `c61844fb73c574b0c17c1690e7df7d7691a105a7`](https://github.com/RemyDegenne/brownian-motion/blob/c61844fb73c574b0c17c1690e7df7d7691a105a7/BrownianMotion/Continuity/IsKolmogorovProcess.lean).

Roots: `ProbabilityTheory.finite_set_bound_of_edist_le`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Rename extended-metric APIs and disambiguate historical helper names. Adjust proof tactics. Select Mathlib imports to avoid replacing the historical `KolmogorovProcess` structure with the newer library definition.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

## Released statement context

- Retain the target declaration closure and source support needed to elaborate it; remove other declarations and modules.
- Replace theorem and lemma bodies, proof-valued declaration bodies, and proof-valued tactic blocks with `sorry`. Preserve declaration types, section parameters, and computational definitions.
