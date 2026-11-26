# Statement-context preparation

- Source qinz1yang/differential-geometry at 3b43fea89fc8d4a42021cbd22d235960b81f6900, originally Lean 4.29.0; compiled with release Lean 4.34.1 and pinned Mathlib.
- Retained the original root signature, every section binder including BoundarylessManifold, and implicit g : SmoothRiemannianMetric I M. Preserved the actual metric alias from the same revision verbatim.
- Omitted unrelated imports and replaced the already-sorry proof by sorry. Fresh extraction verifies the metric alias is the sole local nonproof dependency.
- Source-fragment and Lean source-context equality/rfl probes pass under 4.34.1. A zero-constant witness compiles independently without sorry. Original 4.29 elaborated preservation remains unchecked because the toolchain is unavailable.
- Preliminary agent label compares only the independently bound C0/L-infinity component; human adjudication and release registration remain pending.
