# Lean migration

Source: [https://github.com/RemyDegenne/brownian-motion at `e1110a71a5b96b0e00580afcbf170493b565fa8e`](https://github.com/RemyDegenne/brownian-motion/blob/e1110a71a5b96b0e00580afcbf170493b565fa8e/BrownianMotion/Continuity/IsKolmogorovProcess.lean).

Roots: `ProbabilityTheory.finite_set_bound_of_edist_le`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Rename extended-metric APIs and disambiguate historical helper names. Adjust proof tactics. Select Mathlib imports to avoid replacing the historical `KolmogorovProcess` structure with the newer library definition.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
