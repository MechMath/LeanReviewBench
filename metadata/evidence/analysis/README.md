# Per-input analysis evidence

Each `<batch>/<input-id>.json` binds the current label, reason, review state and
complete root list to the frozen input hash. [index.json](index.json) associates
all 197 input identities with evidence paths and SHA-256 digests:

- 64 retain a detailed review under `analysis`, including all 26 Poincare inputs.
- 130 retain the existing label reason and source references only.
- 3 explicitly record a missing reason; no justification is invented.

`analysis_status` distinguishes these levels. A local summary does not imply
that a detailed proof or human review exists. Source references marked
`historical_locator` describe prior evidence, which may be archive-only.
`upstream_evidence` points to exact upstream record IDs and input associations;
its presence does not endorse the upstream claim for the current snapshot.

Detailed reviews retain mathematical arguments, evidence locations, scope
qualifications, and reviewer information. Superseded `previous_*` fields are
omitted from the embedded review; prior record versions remain in Git history.
Dates and decision provenance remain metadata, not directory organization.
Historical paths inside retained analysis are source locators, not a promise
that every referenced artifact is available locally.

The original 171 binary judgments are human reviewed. All 26 Poincare
judgments are also human confirmed (six aligned and twenty misaligned),
including sixteen accepted by explicit user batch confirmation. Their retained
reviews compare the source and formal statements, check alternative
interpretations, and retain declaration locations.
All 26 Poincare records now have human-selected binary judgments. The
FM-COVERING-before record is aligned under the explicitly adjudicated
positive-dimensional source convention and retains the corrected connected-source
convention. It also documents why the singleton identity would be an applicability
witness if the target were instead interpreted to include dimension zero.
Both parallel-transport records include the final chart-transition
calculation; their reason rewrites are complete. Material scope qualifications
remain in the evidence.
Mathematical separating examples are distinguished from Lean-certified counterexamples.

The concise English reasons and scopes match the label records;
`retained_reason` and `retained_review_scope`, where
present, preserve the historical review in English. Chinese passages were
translated on 2026-11-20 without changing their mathematical content or judgments;
the original wording remains in Git history. Historical claims that inputs were
unchanged refer to the review being quoted. Current input bindings were updated
where the informal text was translated, with the prior hashes recorded in
provenance and the existing Lean checks explicitly reused. Embedded earlier review
states are source provenance, not the current adjudication status. These evidence records must never
be sent to the model as task inputs. Missing reasons and unresolved material qualifications
remain separate from binary labels and reference readiness.
