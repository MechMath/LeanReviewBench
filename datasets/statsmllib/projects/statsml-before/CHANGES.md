# Lean migration

Source: [https://github.com/Lean-MoDS/StatsMLlib at `902b2a0f69b2a63b1d5cb459fb4ece4202087395`](https://github.com/Lean-MoDS/StatsMLlib/blob/902b2a0f69b2a63b1d5cb459fb4ece4202087395/StatsMLlib/LearningTheory/UniformDeviation/Bounds.lean).

Roots: `uniform_deviation_tail_bound_separable_of_pos`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate the selected project modules under `dep` and retain the selected uniform-deviation statement. The source closure and preparation receipts are recorded in `project.json`; no further compatibility edits are described in the input metadata.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
