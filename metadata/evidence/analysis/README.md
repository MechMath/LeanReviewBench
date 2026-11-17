# Per-input analysis evidence

Each `<batch>/<input-id>.json` binds the current label, reason, review state and
complete root list to the frozen input hash. Label records reference its path
and SHA-256. [index.json](index.json) inventories all 171 records:

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

These are provisional evaluation-side records and must never be sent to the
model as task inputs. Missing reasons and unresolved material qualifications
remain separate from binary labels and reference readiness.
