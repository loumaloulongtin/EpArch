/-
EpArch/Mechanisms.lean — Canonical Mechanism Predicates

This module defines the canonical mechanism predicates that health goals
force under agent constraints. These are the "what the system must have"
predicates that design-imposition theorems target.

This file consolidates predicates previously scattered across multiple files into:
1. Abstract mechanism predicates (Prop-level, for agent reasoning)
2. CoreModel mechanism predicates (for Health.lean integration)
3. Mappings between the two levels

## Design

Mechanism predicates answer: "What capability does the system have?"
- NOT whether the capability is used correctly
- NOT the implementation details
- Just: does the mechanism exist?

Bridge theorems prove equivalence (↔) between these predicates and Health.lean capabilities.

-/

import EpArch.Basic
import EpArch.RevisionSafety
import EpArch.Health

namespace EpArch.Mechanisms

open EpArch.RevisionSafety

universe u

/-! ## Abstract Mechanism Predicates (Prop-Level)

These are pure Prop predicates for agent-layer reasoning.
They don't reference CoreModel — just state whether a capability exists.
-/

/-- System has reversibility: actions can be undone. -/
def HasReversibility (canUndo : Prop) : Prop := canUndo

/-- System has cheap validator: verification within bounded cost. -/
def HasCheapValidator (validatorExists : Prop) : Prop := validatorExists

/-- System has export gate: error interception at boundaries. -/
def HasExportGate (gateExists : Prop) : Prop := gateExists

/-- System has revision hooks: deposits can be revised. -/
def HasRevisionHooks (revisionPossible : Prop) : Prop := revisionPossible

/-- System has scoped audit: verification surfaces are bounded. -/
def HasScopedAudit (auditBounded : Prop) : Prop := auditBounded

/-- System has revalidation: claims can be re-verified. -/
def HasRevalidationHook (revalidationPossible : Prop) : Prop := revalidationPossible

/-- System distrusts utterances: utterances alone don't create trust. -/
def DistrustUtterances (utteranceDistrusted : Prop) : Prop := utteranceDistrusted

/-- System separates evidence: statement, evidence, and verification are independently checkable. -/
def EvidenceSeparation (separationExists : Prop) : Prop := separationExists


/-! ## CoreModel Mechanism Predicates

These reference CoreModel/CoreOps and provide the bridge to Health.lean.
-/

/-- CoreModel has revision capability at some bubble. -/
def CoreHasRevision (M : CoreModel) : Prop :=
  ∃ (B : M.sig.Bubble), M.ops.hasRevision B

/-- CoreModel has self-correction capability. -/
def CoreHasSelfCorrection (M : CoreModel) : Prop :=
  ∃ (B : M.sig.Bubble), M.ops.selfCorrects B

/-- CoreModel has verification capability. -/
def CoreHasVerification (M : CoreModel) : Prop :=
  ∃ (B : M.sig.Bubble) (d : M.sig.Deposit) (t : M.sig.Time),
    M.ops.verifyWithin B d t

/-- CoreModel has submission capability. -/
def CoreHasSubmission (M : CoreModel) : Prop :=
  ∃ (a : M.sig.Agent) (B : M.sig.Bubble) (d : M.sig.Deposit),
    M.ops.submit a B d


/-! ## Mechanism Bundle

Convenient bundle for stating "system has all required mechanisms."
-/

/-- Bundle of mechanism capabilities (Prop-level). -/
structure MechanismBundle where
  hasReversibility : Prop
  hasCheapValidator : Prop
  hasExportGate : Prop
  hasRevisionHooks : Prop
  hasScopedAudit : Prop
  hasRevalidation : Prop
  distrustUtterances : Prop
  evidenceSeparation : Prop

/-- A core mechanism suite satisfies five key mechanism predicates. -/
def FullMechanismSuite (M : MechanismBundle) : Prop :=
  HasReversibility M.hasReversibility ∧
  HasCheapValidator M.hasCheapValidator ∧
  HasExportGate M.hasExportGate ∧
  HasRevisionHooks M.hasRevisionHooks ∧
  HasScopedAudit M.hasScopedAudit


/-! ## Mechanism-Health Bridge Theorems

These connect mechanism predicates to Health.lean capabilities.
-/

/-- Core-level revision is equivalent to Health's HasRevisionCapability. -/
theorem revision_hooks_iff_capability (M : CoreModel) :
    CoreHasRevision M ↔ EpArch.HasRevisionCapability M := by
  constructor <;> intro h <;> exact h

/-- Self-correction is equivalent to Health's HasSelfCorrectionCapability. -/
theorem self_correction_iff_capability (M : CoreModel) :
    CoreHasSelfCorrection M ↔ EpArch.HasSelfCorrectionCapability M := by
  constructor <;> intro h <;> exact h


/-! ## Paper-Facing Mechanism Claims

These are the mechanism claims stated in terms of CoreModel
to ensure paper-facing status.
-/

/-- Self-correction requires revision.

    This is exactly RevisionGate M from RevisionSafety.lean. -/
theorem self_correction_requires_revision_paper (M : CoreModel) :
    (∀ B, M.ops.selfCorrects B → M.ops.hasRevision B) ↔ RevisionGate M := by
  constructor <;> intro h <;> exact h


end EpArch.Mechanisms
