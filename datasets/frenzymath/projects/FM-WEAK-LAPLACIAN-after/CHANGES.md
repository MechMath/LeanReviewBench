# Statement-context preparation

- Source frenzymath/Poincare-Conjecture at 6530802c544270722767513028e0045862daa575, direct child of before bb91a091f0b968f8bbe8d861e025a88d82b161be; original Lean 4.32.1.
- Retains the independently sourced informal material bytes and scope from the before input. No narrower replacement target is introduced.
- Adds the actual source IsRiemannianDist definition: install g.toRiemannianMetric, then the pinned Mathlib IsRiemannianManifold predicate. All existing local computational helper source files are unchanged in this direct child commit.
- Preserves full original per-declaration section variables, binder order and omit directives. Proof-only erasure and metricRiesz V := E compatibility annotation follow the verified before preparation.
- Compiled and freshly extracted with Lean 4.34.1. Complete root and 35 computational helper types/values independently checked in migrated context; six proofhelper types checked. Nominal structures preserve source fragments and shared identities. Original Lean 4.32.1 elaborated preservation is unchecked.
- Provisional aligned judgment concerns the specific ambient-distance linkage and test-integral definition interface; human review of the arbitrary-function interface versus source distance-function scope remains pending.
