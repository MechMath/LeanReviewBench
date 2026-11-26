# Lean migration

Source: [https://github.com/fpvandoorn/carleson at `26325e323949418e155a4dc92b9b5a047ef2de82`](https://github.com/fpvandoorn/carleson/blob/26325e323949418e155a4dc92b9b5a047ef2de82/Carleson/MetricCarleson.lean).

Roots: `metric_carleson`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Retain historical ENorm classes under `Legacy212_` names, including their original topology and norm fields. Preserve the historical piecewise norm formula and measurability/finiteness definition of `MemLp`; bridge to modern norms only under the recorded measurability assumptions. Retain the historical two-field `Real.IsConjExponent` structure. Adapt local imports and proof elaboration.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

Before context pruning, compatibility edits affected `Carleson/CoverByBalls.lean`, `Carleson/Defs.lean`, `Carleson/DoublingMeasure.lean`, `Carleson/Legacy212Norm.lean`, `Carleson/ToMathlib/ENorm.lean`, `Carleson/ToMathlib/MeasureReal.lean`, `Carleson/ToMathlib/Misc.lean`, `Carleson/WeakType.lean`.

## Released statement context

- Retain the target declaration closure and source support needed to elaborate it; remove other declarations and modules.
- Replace theorem and lemma bodies, proof-valued declaration bodies, and proof-valued tactic blocks with `sorry`. Preserve declaration types, section parameters, and computational definitions.
