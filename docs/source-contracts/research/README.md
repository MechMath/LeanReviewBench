# Benchmark maintenance

This branch prepares thirteen real-project batches for publication. The data
format is called the project-case format (`paperlean-project-case-1`);
AppliedModelingLib is one source repository, not the format name.
Original OpenAI/OAI, FLT and Kakeya inputs remain excluded.

- [Scope and counts](../README.md)
- [Project-case format and maintenance](PROJECT-CASE-WORKFLOW.md)
- [Upstream evidence and integrity](../metadata/README.md)
- [Statistics and counting limits](PROJECT-CASE-STATS.md)
- [Statement misalignment taxonomy](MISALIGNMENT-TAXONOMY.md)
- [Historical classification of the original 70 misaligned cases](../reports/misalignment-taxonomy-2026-11-10/README.md)
- [Construction method](CONSTRUCTION.md)
- [External dependency configuration](ENVIRONMENT.md)
- [Current layout](DIRECTORY-CLEANUP.md)
- [Validation and tests](testing.md)
- [Evaluation tools and setup](../scripts/evaluation/README.md)
- [Versioned evaluation contract](../protocol/v1/README.md)

Run `python3 scripts/data/check_release_candidate.py` for current scope, input,
upstream evidence and metadata checks. The candidate has no frozen native evaluation
package yet. Evaluation tools accept explicitly supplied packages with complete
formal context; project CSV files are not themselves runnable task exports.
