import Mathlib

import dep.LG21TestOptionalPolicies.PostPaperAudit

/-!
# Human Review Interface: LG21 Test-Optional Policies

This is the canonical human-review surface for
*Test-optional Policies: Overcoming Strategic Behavior and Informational Gaps*.
It exposes one compact row per paper-facing definition or named result, with
regime variants only where the paper states the result separately for optional
reporting and report-required policies.

Implementation endpoints, proof-route variants, diagnostics, and reusable
bridge lemmas live in `ProofInterface.lean` and `PostPaperAudit.lean`.
-/

namespace LG21TestOptionalPolicies

namespace PaperInterface

/-! ## Source Definitions -/

/- Definition 1: source equilibrium for test-taking and reporting decisions. -/
abbrev theorem3_1_optional_reporting :=
  @PostPaperAudit.audit_theorem3_1_section3_optional_reporting

/- Theorem 3.1: strategic withholding under report-required policies. -/
end PaperInterface

end LG21TestOptionalPolicies
