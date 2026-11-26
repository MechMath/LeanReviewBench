# Statement-context preparation

- Pinned source: frenzymath/Poincare-Conjecture, f5661a1a73a7104af9e65024edd8a569d49ba981; original Lean 4.32.1.
- Migrated to release Lean 4.34.1 and pinned Mathlib. Retained 13 actual source aliases/definitions and their computational bodies verbatim; omitted unrelated proofs, helpers and imports. No metric, chart, derivative or Christoffel definition was stubbed.
- The original Module.Finite/FiniteDimensional duplicate binder is retained in the separate source-context preservation probe. All 13 types and values agree definitionally with the slice under Lean 4.34.1. Existing overlapping-instance warnings are retained.
- Fresh statement extraction passed. Original Lean 4.32.1 elaborated preservation is not certified because that toolchain is unavailable. Human review and release registration remain pending.
