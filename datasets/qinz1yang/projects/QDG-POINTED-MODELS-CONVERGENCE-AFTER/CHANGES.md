Actual source root PointedModelsConverge_S13 only. PointedSmoothConverges_S13 is not covered.

Target Lean4.34.1; original Lean4.35.0-rc3 unavailable and not checked. Exact before/after source commits are recorded separately.

All metric/norm/covariant-derivative, curvature, volume, map and tensor computational definitions use actual pinned source values. Theorem/lemma proofs in support modules are erased; data-valued tactics remain. Proof erasure is currently partial.

Compatibility annotations: RiemannianMetricComplete uses explicit ((⊤ : ℕ∞) : WithTop ℕ∞) in a proof fact to resolve infinity notation; the original source instance-suppression attribute is restored. A local proof of NeZero (Module.finrank ℝ ThreeSpace) is supplied for the actual dimension-three alias. Original variable order, omit directives, implicit_reducible attributes and explicit variable (I M) binder for volume are preserved.

After adds actual canonical limit reference metric and exact canonicalSourceData domain equality. It is not automatically assigned aligned.
