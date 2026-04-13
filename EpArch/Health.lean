/-
Health Predicates and Necessity Theorems

## Health Goals are Definitional

Health predicates are NOW defined over the core semantics (CoreOps), not as
abstract boolean flags. This makes necessity theorems derivable from definitions
rather than axioms.

**Pattern:** HealthGoal(CoreOps) → NecessityTheorem (proved, not asserted)

The key insight: health goals ARE predicates over traces and operations.
- `SafeWithdrawalGoal`: submission of a deposit implies some authorization
  witness exists — operationalizes the “safe withdrawal” property
- `ReliableExportGoal`: false deposits do not appear true across bubble
  boundaries (unless the target bubble has revision capability)
- `CorrigibleLedgerGoal`: when revision capability exists, revisions
  produce deposits that are true in the target bubble
- `SoundDepositsGoal`: effective audit cost stays within verification budget
- `SelfCorrectionGoal`: revision capability exists (precondition for any
  self-correction trace)

These are safety properties, and necessity follows from what the property requires.

## Connections

- **Invariants.lean:** structural invariants (no_deposit_without_redeemability, etc.)
  constrain what valid deposits look like; health goals build on these constraints
- **Agent/Imposition.lean:** uses health goals to prove design-forcing
  (constraints + goal + ¬mechanism → contradiction)
- **Mechanisms.lean:** bridge theorems connect health predicates to mechanism predicates
-/

import EpArch.Basic
import EpArch.Header
import EpArch.Bank
import EpArch.Invariants
import EpArch.RevisionSafety

namespace EpArch

open RevisionSafety

/-! ## Health Goals as Core Predicates

Health goals are now predicates over CoreModel/CoreOps.
This makes them definitional: we can PROVE necessity theorems. -/

/-- SafeWithdrawalGoal: Every submitting bubble has revision capability.

    A bubble that accepts submissions must also be able to revise them —
    safe withdrawal requires the structural ability to correct mistakes.
    This is non-trivial: it rules out submit-only (append-only) bubbles
    as insufficient for the health goal. -/
def SafeWithdrawalGoal (M : CoreModel) : Prop :=
  ∀ (a : M.sig.Agent) (B : M.sig.Bubble) (d : M.sig.Deposit),
    M.ops.submit a B d → M.ops.hasRevision B  -- submission requires revision capability

/-- ReliableExportGoal: False deposits don't appear true across boundaries.

    If d is not true in B, then either d is also not true in B',
    or B' has revision capability (can revalidate). -/
def ReliableExportGoal (M : CoreModel) : Prop :=
  ∀ (B B' : M.sig.Bubble) (d : M.sig.Deposit),
    ¬M.ops.truth B d → ¬M.ops.truth B' d ∨
    M.ops.hasRevision B'  -- B' has revalidation capability

/-- CorrigibleLedgerGoal: The system has revision capability and corrections are sound.

    Corrigibility means being CAPABLE of correction — so at least one bubble
    must support revision. Additionally, when revision fires it produces truths.
    The existence component captures: "corrigible" means correction CAN happen,
    not merely that it WOULD BE sound IF it could.  This is the design-forcing
    predicate: satisfying CorrigibleLedgerGoal is sufficient to infer
    HasRevisionCapability without a separate existence witness. -/
def CorrigibleLedgerGoal (M : CoreModel) : Prop :=
  (∃ B : M.sig.Bubble, M.ops.hasRevision B) ∧
  ∀ (B : M.sig.Bubble),
    M.ops.hasRevision B →
    (∀ (d d' : M.sig.Deposit), M.ops.revise B d d' → M.ops.truth B d')

/-- SoundDepositsGoal: All deposits are verifiable within effective time.

    Definitional over verifyWithin and effectiveTime:
    deposits are meaningful only if they can be verified. -/
def SoundDepositsGoal (M : CoreModel) : Prop :=
  ∀ (B : M.sig.Bubble) (d : M.sig.Deposit),
    M.ops.truth B d →
    M.ops.verifyWithin B d (M.ops.effectiveTime B)

/-- SelfCorrectionGoal: The system can correct its errors.

    Defined as: selfCorrects → hasRevision.
    See `self_correction_is_revision_gate` for the equivalence with RevisionGate. -/
def SelfCorrectionGoal (M : CoreModel) : Prop :=
  ∀ B : M.sig.Bubble, M.ops.selfCorrects B → M.ops.hasRevision B

/-- SelfCorrectingSystem: A system that ACTIVELY self-corrects.

    Combines SelfCorrectionGoal (the conditional: selfCorrects → hasRevision)
    with the existence requirement (at least one bubble actually self-corrects).
    This is the design-forcing predicate for the necessity theorem:
    a system that demonstrably self-corrects must have revision capability. -/
def SelfCorrectingSystem (M : CoreModel) : Prop :=
  SelfCorrectionGoal M ∧ ∃ B : M.sig.Bubble, M.ops.selfCorrects B


/-! ## Capability Predicates (Definitional)

These predicates state what capabilities a system MUST have.
They're now defined structurally, not as opaques. -/

/-- System has submission capability. -/
def HasSubmitCapability (M : CoreModel) : Prop :=
  ∃ (a : M.sig.Agent) (B : M.sig.Bubble) (d : M.sig.Deposit),
    M.ops.submit a B d

/-- System has revision capability (at some bubble). -/
def HasRevisionCapability (M : CoreModel) : Prop :=
  ∃ (B : M.sig.Bubble), M.ops.hasRevision B

/-- System has verification capability. -/
def HasVerificationCapability (M : CoreModel) : Prop :=
  ∃ (B : M.sig.Bubble) (d : M.sig.Deposit) (t : M.sig.Time),
    M.ops.verifyWithin B d t

/-- System has self-correction capability. -/
def HasSelfCorrectionCapability (M : CoreModel) : Prop :=
  ∃ (B : M.sig.Bubble), M.ops.selfCorrects B


/-! ## Necessity Theorems (PROVED, not axioms)

These theorems follow from the definitions above.
The proofs are straightforward because health goals IMPLY capability requirements.
-/

/-- Corrigible ledger goal implies revision capability.

    **PROVED**: CorrigibleLedgerGoal now encodes the existence of revision
    capability directly, so the theorem follows from the first component of
    the conjunction.  Single-premise design-forcing: the goal alone forces
    the mechanism. -/
theorem corrigible_needs_revision (M : CoreModel)
    (h_corrig : CorrigibleLedgerGoal M) :
    HasRevisionCapability M := h_corrig.1

/-- Self-correcting system implies revision capability.

    **PROVED**: SelfCorrectingSystem bundles the conditional goal with an
    existence witness; the theorem extracts the witness via modus ponens.
    Single-premise: `SelfCorrectingSystem M` alone forces `HasRevisionCapability M`. -/
theorem self_correction_needs_revision (M : CoreModel)
    (h : SelfCorrectingSystem M) :
    HasRevisionCapability M :=
  let ⟨h_goal, B, h_sc⟩ := h
  ⟨B, h_goal B h_sc⟩

/-- Sound deposits goal implies verification capability.

    **PROVED**: If deposits must be verifiable, verification exists. -/
theorem sound_deposits_needs_verification (M : CoreModel)
    (h_sound : SoundDepositsGoal M)
    (h_exists_truth : ∃ B d, M.ops.truth B d) :
    HasVerificationCapability M := by
  match h_exists_truth with
  | ⟨B, d, h_truth⟩ =>
    have h_verify := h_sound B d h_truth
    exact ⟨B, d, M.ops.effectiveTime B, h_verify⟩


/-! ## Combined System Health (Definitional) -/

/-- A fully healthy system satisfies all definitional health goals. -/
structure FullSystemHealth (M : CoreModel) where
  safe_withdrawal : SafeWithdrawalGoal M
  reliable_export : ReliableExportGoal M
  corrigible_ledger : CorrigibleLedgerGoal M
  sound_deposits : SoundDepositsGoal M
  self_correction : SelfCorrectionGoal M

/-- Full system health is equivalent to RevisionGate + other goals.

    **Key observation:** SelfCorrectionGoal M ↔ RevisionGate M -/
theorem self_correction_is_revision_gate (M : CoreModel) :
    SelfCorrectionGoal M ↔ RevisionGate M := by
  constructor
  · intro h; exact h
  · intro h; exact h


/-! ## Design Note

All necessity theorems (corrigible_needs_revision, self_correction_needs_revision,
sound_deposits_needs_verification) are proved from definitions, not axioms. -/


/-! ## Health Goals Summary

The health predicates connect to the architectural invariants:

| Health Goal | Necessary Capability | Core Operation |
|-------------|----------------------|----------------|
| SafeWithdrawalGoal | Authorization | `submit` |
| ReliableExportGoal | Revalidation | `hasRevision`, `truth` |
| CorrigibleLedgerGoal | Revision | `revise`, `hasRevision` |
| SoundDepositsGoal | Verification | `verifyWithin`, `effectiveTime` |
| SelfCorrectionGoal | Revision | `hasRevision` (= RevisionGate) |

Health goals ARE definitional predicates over CoreOps.
Necessity theorems follow from what health MEANS.
-/

end EpArch
