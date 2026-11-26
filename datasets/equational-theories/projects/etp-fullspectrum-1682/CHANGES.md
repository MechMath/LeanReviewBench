# Lean migration

Source: [https://github.com/teorth/equational_theories at `8b87204d5b201e1cf6c69b8dcabb0558109bee00`](https://github.com/teorth/equational_theories).

Roots: `FullSpectrum.full_spectrum_Equation1682`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate project modules and adapt the recorded Lean/Mathlib API interfaces. Retain the author-written target, non-proof definitions and generated mathematical data. Certificate resources used by retained definitions remain part of the input.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

The historical migration recorded compatibility edits in 4 source modules.

## Released statement context

- Retain the target declaration closure and source support needed to elaborate it; remove other declarations and modules.
- Replace theorem and lemma bodies, proof-valued declaration bodies, and proof-valued tactic blocks with `sorry`. Preserve declaration types, section parameters, and computational definitions.
- Materialize required generated equation/law declarations as ordinary Lean declarations; omit the upstream search-result registration attribute.
