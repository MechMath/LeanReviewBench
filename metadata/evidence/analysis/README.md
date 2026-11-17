# Per-input analysis evidence

Each `<batch>/<input-id>.json` binds the current label, reason, review state and
complete root list to the frozen input hash. [index.json](index.json) associates
all 171 input identities with evidence paths and SHA-256 digests:

- 38 retain a detailed review under `analysis`.
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

The binary judgments are human reviewed. Their concise English reasons and scopes
match the label records; `retained_reason` and `retained_review_scope`, where
present, preserve the original wording. Embedded earlier review states are source
provenance, not the current adjudication status. These evidence records must never
be sent to the model as task inputs. Missing reasons and unresolved material qualifications
remain separate from binary labels and reference readiness.
