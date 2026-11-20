# FM-BISHOP-before

Pinned source: `frenzymath/Poincare-Conjecture@4dff1831c65f51855a70dc3c4ff03bea49a5619e`.

Retained the selected complete declaration types and all local computational definitions required by their statement closure. Replaced theorem proofs with `sorry`; computational definitions remain intact. Replaced proof-only upstream imports with Mathlib support in Lean 4.34.1.

Compilation, fresh LeanTrace extraction and migrated-source-versus-slice preservation passed. The historical leanprover/lean4:v4.32.1 environment was not replayed; original-environment elaborated preservation remains pending.

The informal target is independently sourced and provisionally bound. Agent labels are outside this input and await human review. This package is unregistered staging material.
