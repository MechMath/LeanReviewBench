# Lean migration

Source: [https://github.com/ImperialCollegeLondon/FLT at `8c4bb0b2046a1d564623057bb359212f92e0d1f2`](https://github.com/ImperialCollegeLondon/FLT/blob/8c4bb0b2046a1d564623057bb359212f92e0d1f2/FLT/DivisionAlgebra/Finiteness.lean).

Roots: `NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Adapt imports, tensor-induction APIs, typeclass elaboration and completion-wrapper coercions. Rename the historical local `Field.absoluteGaloisGroup.map` to `flt_map` where needed to avoid a library-name collision, updating its local references.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

Completion-wrapper adaptations follow upstream #1100 and #1121; tensor-induction adaptations follow #1192. Completion maps use the corresponding wrapper equivalences/maps; adele notation collisions are expanded to the existing definitions.
