/-
EpArch.Theorems.Cases.FakeBarn — Fake Barn Case: E-Field Failure

Structures and theorems for the Fake Barn SEV failure mode:
- FailureMode / ErrorModelCoverage / E_coverage_fails: the E-gap proxy
- FakeBarnCase: structural invariant (e_certified required at construction)
- fake_barn_is_E_failure: unconditional; certified at construction time
- canonical_fake_barn: the "Fake Barn County" example

Proxy interpretation: `ErrorModelCoverage.unmodeled_threats.any nearby` means
the error model has coverage gaps.

Future work: Modal structures for "nearby possible worlds".
-/
import EpArch.Basic
import EpArch.Semantics.StepSemantics

namespace EpArch

open StepSemantics

universe u

variable {PropLike Standard ErrorModel Provenance Reason Evidence : Type u}

/-! ### Fake Barn Case: E-Field Failure (Unmodeled Environmental Threat)

    The E-coverage concept ("nearby failure modes") is intentionally
    schematic. We don't need full modal semantics—just a threat-coverage relation.

    This proxy treats "nearby" as a parameterized set selector (by region,
    context class, etc.) rather than solving modal metaphysics.

    Proxy interpretation: `ErrorModelCoverage.unmodeled_threats.any nearby` means
    the error model has coverage gaps. Theorem: FakeBarnInstance → ¬Coverage.

    Future work: Modal structures for "nearby possible worlds".
-/

/-- A failure mode that could defeat the claim. -/
structure FailureMode where
  /-- Description of the threat (e.g., "deceptive replica in environment") -/
  threat : String
  /-- Is this failure mode "nearby" (modally close / plausible)? -/
  nearby : Bool

/-- Error model coverage: which failure modes are included?

    An error model is adequate if it includes all nearby failure modes. -/
structure ErrorModelCoverage where
  /-- Failure modes the agent's error model considers -/
  modeled_threats : List FailureMode
  /-- Failure modes present in the environment but not modeled -/
  unmodeled_threats : List FailureMode

/-- E-field fails when nearby threats are unmodeled. -/
def E_coverage_fails (cov : ErrorModelCoverage) : Bool :=
  cov.unmodeled_threats.any (·.nearby)

/-- Fake Barn case structure.

    The "Fake Barn County" case:
    - Agent sees a real barn, correctly identifies it
    - But is surrounded by fake barns (unmodeled environmental threat)
    - Error model E didn't include "nearby deceptive replicas"

    We explicitly represent the unmodeled nearby failure mode,
    not just a Bool flag. -/
structure FakeBarnCase where
  /-- The agent's claim (e.g., "that's a barn") -/
  claim : PropLike
  /-- S-field passes (meets threshold) -/
  S_passes : Bool
  /-- Error model coverage showing unmodeled nearby threats -/
  e_coverage : ErrorModelCoverage
  /-- V-field passes (genuine provenance) -/
  V_passes : Bool
  /-- Structural certification: the error model coverage definitionally fails -/
  e_certified : E_coverage_fails e_coverage = true

/-- E-field is inadequate when error model has unmodeled nearby threats. -/
def barn_case_E_inadequate (fb : FakeBarnCase (PropLike := PropLike)) : Prop :=
  E_coverage_fails fb.e_coverage = true

/-- CANONICAL Fake Barn case: S and V pass, but nearby threat unmodeled.

    Fake Barn County example:
    - modeled_threats: [] (agent just uses "looks like a barn")
    - unmodeled_threats: [{threat: "facades in region", nearby: true}]
    - E_coverage_fails = true because nearby threat is unmodeled -/
def canonical_fake_barn (P : PropLike) : FakeBarnCase (PropLike := PropLike) :=
  { claim := P,
    S_passes := true,
    e_coverage := {
      modeled_threats := [],
      unmodeled_threats := [⟨"deceptive facades in region", true⟩]  -- nearby = true
    },
    V_passes := true,
    e_certified := rfl }

/-- IsFakeBarnCase: A case is a genuine Fake Barn case iff:
    1. S passes (meets threshold)
    2. V passes (genuine provenance)
    3. E fails (unmodeled nearby threats exist)

    The definitional characterization: E failed to include the nearby failure mode. -/
def IsFakeBarnCase (fb : FakeBarnCase (PropLike := PropLike)) : Prop :=
  fb.S_passes = true ∧ fb.V_passes = true ∧ E_coverage_fails fb.e_coverage = true

/-- Fake Barn cases route to E-failure.

    Unconditional: the conclusion follows directly from the structural
    `e_certified` field, which is certified at construction time. -/
theorem fake_barn_is_E_failure (fb : FakeBarnCase (PropLike := PropLike)) :
    barn_case_E_inadequate fb :=
  fb.e_certified

/-- Canonical Fake Barn case satisfies IsFakeBarnCase. -/
theorem canonical_fake_barn_is_fake_barn (P : PropLike) :
    IsFakeBarnCase (canonical_fake_barn P) :=
  ⟨rfl, rfl, rfl⟩

end EpArch
