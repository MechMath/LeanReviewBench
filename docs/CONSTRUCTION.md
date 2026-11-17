# Case construction method

The 171 released inputs are registered in `datasets/project-cases.json`.
Their source repository, commit and selected roots are recorded in each
`project.json`; the independently sourced mathematical target is in
`informal.jsonl`. See the [data contract](DATA-FORMAT.md) and
[generated statistics](STATISTICS.md).

1. Identify a historical formalization and an independent informal target.
   Preserve the selected revision, mathematical qualifications, and before/after
   relationships. A repaired successor is a separate input.
2. Migrate the required local source to the pinned Lean 4.34.1 environment.
   Record compatibility changes briefly in the input's `CHANGES.md`.
   Preserve mathematical definitions and statements, including reviewed errors.
   Exact upstream revisions provide the original full sources.
3. Use LeanTrace to obtain the roots' statement dependency closure, following
   types and non-proof definition values. For multi-root inputs, retain their
   joint closure. Keep source support needed for elaboration, including notation,
   aliases, instances and compiler simplification declarations.
4. Retain the selected Lean declarations in the existing `formal/Main.lean`
   and `formal/dep/` layout. Replace theorem/lemma and proof-valued declaration
   bodies with `sorry`; erase proof-valued tactic blocks inside definitions.
   Preserve computational definitions and tactic blocks that construct data.
   Keep section parameters and source type annotations when erasing proofs.
   Materialize required generated ETP equations, laws and certificate tables directly.
5. Compile the packaged context and extract a fresh graph from its Lean files.
   Compare the roots and necessary non-proof declarations against their original
   elaborated types and values, allowing proof irrelevance and source-neutral
   binder/let annotations. These checks validate statement contexts, rather than
   certify the original theorem proofs.
6. Record compilation, extraction and preservation results in
   `metadata/validation.json`, bound to input/formal-source digests and roots.
   Keep generated graphs and detailed processing outputs in ignored build directories. Preserve binary judgments, their reasons, taxonomy assignments and
   source evidence when the mathematical content is unchanged. Keep these
   annotations outside model-visible inputs.

All 171 current contexts have recorded compilation and fresh extraction results in
`metadata/validation.json`. Graph files are not part of the release. Required non-Lean resources remain beside their Lean
users; Mathlib and Cslib remain pinned external libraries. EconCSLib belongs to
the historical AppliedModelingLib sources and is vendored only where required
under `formal/dep/`. Its historical source variations remain input-specific.

The released Lean contexts and per-input migration notes are the maintained
artifacts. Reconstructing complete upstream projects or retaining executable
migration histories is unnecessary for ordinary benchmark use. Build caches,
processing scripts and temporary logs are not dataset inputs.

Optional compilation/extraction uses the [configured environment](ENVIRONMENT.md).
Known LeanTrace integration issues are tracked in
[issue #2](https://github.com/MechMath/LeanReviewBench/issues/2).
The model-input protocol remains a separate
[discussion](https://github.com/MechMath/LeanReviewBench/issues/1).
