# Lean migration

Source: [https://github.com/AlexKontorovich/PrimeNumberTheoremAnd at `657ac0e5cf42c45b03b93a662fd8237b6b0be49f`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/657ac0e5cf42c45b03b93a662fd8237b6b0be49f/PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean).

Roots: `ArithmeticFunction.pow_divisors_mul_injective`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Package the independently migrated historical formal snapshot and relocate local imports. Retain the mathematical formulation of that snapshot, including historical admissions; textual before/after pairs may share the same formal snapshot.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
