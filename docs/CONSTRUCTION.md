# Case construction method

The canonical data are the batches registered in
`datasets/project-cases.json`. Follow the [project format and status rules](DATA-FORMAT.md)
and use the [generated statistics](STATISTICS.md). The registered inventory defines the released scope.

1. Screen one repository per branch. Record upstream pin and license, searched
   commits/issues/PRs, candidate root families, excluded leads and reasons.
   Use historical intermediate versions where useful; both aligned controls
   and confusing or misaligned statements are eligible.
2. Freeze each root revision and an independently sourced informal target.
   Record exact source version, locator, excerpt, definitions, domains and
   endpoint conventions. Missing access is a review gap, not a reason to drop
   an otherwise extracted case: retain the input and disclose the missing target.
3. Extract the historical declaration and necessary local definition/import
   closure with pinned Lean/Mathlib/Cslib. Keep external libraries external.
   Apply only documented compatibility edits that preserve Formal semantics;
   keep exact patches and never replace a negative with a repaired successor.
   Preserve historical proof holes and disclose axioms. Defer costly closures
   explicitly rather than inserting new holes to manufacture an extraction.
4. Compile and export actual LeanTrace dependency contexts in default and
   explicit modes. Package the local closure as `formal/Main.lean` plus `dep/`,
   recompile/re-extract after relocation, and compare public declaration
   types/definition values, selected roots and axiom dependencies. Retain
   successful receipts and indispensable evidence; send new temporary outputs
   to `build/construction/<repo>/<run>/`.
5. Retain explicit upstream statements with exact excerpts, original URLs,
   source versions and input bindings in `metadata/evidence/upstream/`.
   Skip generic repair leads and local model judgments. Preserve upstream
   qualifications and AI-use disclosures. These claims are not scoring labels.
6. Admit usable and unresolved extracted inputs into project-case layout. Missing main
   statements have empty `informal.jsonl`, null `informal_id`, undetermined
   status and evaluation eligibility disabled. Never invent a target.
   Give reciprocal before/after links and shared family splits; an after
   version need not be aligned. Keep unextracted deferred leads outside totals.
7. Check project hashes, source bindings, graph/receipt evidence and statistics.
   Keep reviewed labels outside model inputs; final scoring references need a separate export-bound review
   contract and review. Keep related versions in the same split and preserve input identities when updating metadata.

The published tools provide a shared compiler and configurable tool resolution, not a complete pipeline for rebuilding every case from its upstream repository. Historical source acquisition and extraction recipes remain in the pinned research archive identified by `metadata/release.json`. Retaining historical receipts does not establish fresh compilation of the current checkout.

See [data format](DATA-FORMAT.md), [environment](ENVIRONMENT.md), [maintenance](MAINTENANCE.md), and the [taxonomy standard](../metadata/taxonomy/standard.md). Binary alignment verdicts are human reviewed; taxonomy assignments have their own review state.
