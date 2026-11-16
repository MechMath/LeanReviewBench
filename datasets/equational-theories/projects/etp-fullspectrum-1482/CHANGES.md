# Staged source and compatibility

Original source and author-written target are frozen at 8b87204d5b201e1cf6c69b8dcabb0558109bee00. Main.lean only imports the original target module.

Compatibility patch changes 4 source modules; it preserves original theorem targets, definitions and generated data, except transparent API representation updates documented in the staging report. No new sorry or axiom is introduced. Original proof holes elsewhere, if any, remain visible in the source archive. Root axiom audits are retained with successful graph exports.

Compilation: passed. Graph modes: 2/2. Labels remain undetermined.

2026-11-13: relocated repository modules under formal/dep and prefixed local imports with dep. Declaration names and proof bodies unchanged. Historical receipts apply to pre-relocation sources; new receipt tracked separately.
