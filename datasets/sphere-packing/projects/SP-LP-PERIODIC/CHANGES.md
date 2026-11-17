# Lean migration

Source: [https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean at `77cf0a0c104f2e31501eab04d88bbc068d61c169`](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/77cf0a0c104f2e31501eab04d88bbc068d61c169/SpherePacking/CohnElkies/LPBound.lean).

Roots: `LinearProgrammingBound'`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate imports and adapt the historical Mathlib interfaces. Compatibility work includes explicit matrix/group membership arguments, coercions and proof elaboration. Retain historical Fourier, cutoff and norm definitions rather than substituting the repaired successor.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

Recorded compatibility edits affect `SpherePacking/Basic/PeriodicPacking.lean`.
