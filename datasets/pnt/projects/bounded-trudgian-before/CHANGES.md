# Lean migration

Source: [https://github.com/AlexKontorovich/PrimeNumberTheoremAnd at `fc3f35017ee842bccf0d887980e8e22dda1583ab`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/fc3f35017ee842bccf0d887980e8e22dda1583ab/PrimeNumberTheoremAnd/IEANTN/SecondarySummary.lean).

Roots: `Trudgian2016.theorem_2`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Package the independently migrated historical formal snapshot and relocate local imports. Retain the mathematical formulation of that snapshot, including historical admissions; textual before/after pairs may share the same formal snapshot.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
