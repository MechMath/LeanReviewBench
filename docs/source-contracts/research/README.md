# Benchmark maintenance

This branch prepares thirteen real-project batches for publication. The data
format is called the project-case format (`paperlean-project-case-1`);
AppliedModelingLib is one source repository, not the format name.
Original OpenAI/OAI, FLT and Kakeya inputs remain excluded.

- [Scope and counts](https://github.com/MechMath/PaperLeanBench/blob/2f471585a4b71adb32f6e3fac214e366ce8979ae/README.md)
- [Project-case format and maintenance](https://github.com/MechMath/PaperLeanBench/blob/2f471585a4b71adb32f6e3fac214e366ce8979ae/docs/PROJECT-CASE-WORKFLOW.md)
- [Upstream evidence and integrity](https://github.com/MechMath/PaperLeanBench/blob/2f471585a4b71adb32f6e3fac214e366ce8979ae/metadata/README.md)
- [Statistics and counting limits](https://github.com/MechMath/PaperLeanBench/blob/2f471585a4b71adb32f6e3fac214e366ce8979ae/docs/PROJECT-CASE-STATS.md)
- [Statement misalignment taxonomy](https://github.com/MechMath/PaperLeanBench/blob/2f471585a4b71adb32f6e3fac214e366ce8979ae/docs/MISALIGNMENT-TAXONOMY.md)
- [Current misalignment classifications](../../../metadata/taxonomy/README.md)
- [Construction method](https://github.com/MechMath/PaperLeanBench/blob/2f471585a4b71adb32f6e3fac214e366ce8979ae/docs/CONSTRUCTION.md)
- [External dependency configuration](https://github.com/MechMath/PaperLeanBench/blob/2f471585a4b71adb32f6e3fac214e366ce8979ae/docs/ENVIRONMENT.md)
- [Current layout](https://github.com/MechMath/PaperLeanBench/blob/2f471585a4b71adb32f6e3fac214e366ce8979ae/docs/DIRECTORY-CLEANUP.md)
- [Validation and tests](https://github.com/MechMath/PaperLeanBench/blob/2f471585a4b71adb32f6e3fac214e366ce8979ae/docs/testing.md)
- [Evaluation tools and setup](https://github.com/MechMath/PaperLeanBench/blob/2f471585a4b71adb32f6e3fac214e366ce8979ae/scripts/evaluation/README.md)
- [Versioned evaluation contract](https://github.com/MechMath/PaperLeanBench/blob/2f471585a4b71adb32f6e3fac214e366ce8979ae/protocol/v1/README.md)

Run `python3 scripts/data/check_release_candidate.py` for current scope, input,
upstream evidence and metadata checks. The candidate has no frozen native evaluation
package yet. Evaluation tools accept explicitly supplied packages with complete
formal context; project CSV files are not themselves runnable task exports.
