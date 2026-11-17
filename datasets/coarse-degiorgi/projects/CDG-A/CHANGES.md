# Lean migration

Source: [https://github.com/scottnarmstrong/CoarseDeGiorgi at `200c40c9c55a5e19188739d27466ddffcb2660c4`](https://github.com/scottnarmstrong/CoarseDeGiorgi/blob/200c40c9c55a5e19188739d27466ddffcb2660c4/CoarseDeGiorgi/Statements/LocalBoundedness.lean).

Roots: `CoarseDeGiorgi.local_boundedness`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate local imports. Where recorded below, adjust proof-local elaboration in selection adapters; retain the target statements and data definitions.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

These changes prepare historical Formal for Lean 4.34.1. Upstream before/after fixes are separate snapshots; the compatibility port does not replace the selected historical revision.

Packaging additionally relocates the target module to `formal/Main.lean`, places retained local imports under `formal/dep/`, and rewrites only local import paths. Namespaces, declaration names, binders, definition values and proof source are retained.

Recorded compatibility edits affect `CoarseDeGiorgi/Harnack/WeakHarnack/SelectionAdapters.lean`.
