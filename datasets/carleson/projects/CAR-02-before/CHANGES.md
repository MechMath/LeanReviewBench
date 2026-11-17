# Lean migration

Source: [https://github.com/fpvandoorn/carleson at `f005a0fe7be71905a7bbe2f85b7ecd23e84a637f`](https://github.com/fpvandoorn/carleson/blob/f005a0fe7be71905a7bbe2f85b7ecd23e84a637f/Carleson/LinearizedMetricCarleson.lean).

Roots: `linearized_metric_carleson`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Preserve the historical unguarded `eLpNorm` formula as `MeasureTheory.legacy297Norm` and its original measurability/finiteness predicate as `Legacy297MemLp`. Adapt historical ENorm/WeakType references and proof elaboration. Retain the selected implicit phase and the snapshot-specific presence or absence of `toReal`; do not add a universal phase premise.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

Recorded compatibility edits affect `Carleson/Defs.lean`, `Carleson/Legacy297Norm.lean`, `Carleson/ToMathlib/CoverByBalls.lean`, `Carleson/ToMathlib/Data/ENNReal.lean`, `Carleson/ToMathlib/DoublingMeasure.lean`, `Carleson/ToMathlib/ENorm.lean`, `Carleson/ToMathlib/Misc.lean`, `Carleson/ToMathlib/WeakType.lean`.
