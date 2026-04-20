/-
EpArch.Mechanisms — Canonical Mechanism Predicates

This module defines the canonical mechanism predicates that health goals
force under agent constraints. These are the "what the system must have"
predicates that design-imposition theorems target.

This file consolidates predicates previously scattered across multiple files into:
1. Abstract mechanism predicates (Prop-level, for agent reasoning)
2. CoreModel mechanism predicates (for EpArch.Health integration)
3. CoreModel-to-Scenario projections and bridge theorems (Imposition wiring)

## Design

Mechanism predicates answer: "What capability does the system have?"
- NOT whether the capability is used correctly
- NOT the implementation details
- Just: does the mechanism exist?

Bridge theorems connect CoreModel predicates to the Imposition necessity results
in EpArch.Agent.Imposition: each states that a CoreModel lacking capability X
cannot satisfy the corresponding architectural goal for the canonical failure-mode
scenario. Proofs delegate to the counterexample proofs in Imposition.

-/

import EpArch.Basic
import EpArch.Semantics.RevisionSafety
import EpArch.Health
import EpArch.Agent.Imposition

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

These reference CoreModel/CoreOps and provide the bridge to EpArch.Health.
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

/-- CoreModel has cheap validator: verification can be completed within the effective time
    budget at some bubble, enabling cost-bounded claim validation. -/
def CoreHasCheapValidator (M : CoreModel) : Prop :=
  ∃ (B : M.sig.Bubble) (d : M.sig.Deposit),
    M.ops.verifyWithin B d (M.ops.effectiveTime B)

/-- CoreModel has export gate: some deposit is verifiable as truth at some bubble,
    enabling error interception at deposit export boundaries. -/
def CoreHasExportGate (M : CoreModel) : Prop :=
  ∃ (B : M.sig.Bubble) (d : M.sig.Deposit), M.ops.truth B d


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


/-! ## CoreModel-to-Scenario Projections

Projection functions embed CoreModel failure modes into the Imposition scenario types.
Each function maps a CoreModel lacking capability X to the concrete scenario that
witnesses the X failure mode. The ¬CoreHasX hypothesis documents that the projection
is valid precisely because the model lacks the capability.
-/

section
open EpArch.Agent

/-- Project a CoreModel without revision into a withdrawal scenario.
    The scenario has hasReversibility = false, reflecting that no bubble in M
    carries a revision operator. -/
def coreToWithdrawalScenario (_M : CoreModel) (_h_no_rev : ¬CoreHasRevision _M) :
    WithdrawalScenario where
  mistakeOccurred  := true
  harmIsPermanent  := true
  hasReversibility := false
  no_rev_permanent := fun _ _ => rfl

/-- Project a CoreModel without cheap validator into a deposit scenario.
    The scenario witnesses cost overrun: claim cost = budget + 1 exceeds budget. -/
def coreToDepositScenario (_M : CoreModel) (_h_no_val : ¬CoreHasCheapValidator _M)
    (budget : Nat) : DepositScenario :=
  deposit_counterexample budget

/-- Project a CoreModel without export gate into an export scenario.
    The scenario witnesses silent error propagation: observation incorrect, export not blocked. -/
def coreToExportScenario (_M : CoreModel) (_h_no_gate : ¬CoreHasExportGate _M) :
    ExportScenario :=
  export_counterexample


/-! ## CoreModel Bridge Theorems

These theorems connect the Imposition necessity results to the CoreModel. Each theorem
states that a CoreModel lacking capability X cannot satisfy the corresponding
architectural goal for the canonical failure-mode scenario. Proofs delegate to the
genuine counterexample proofs in EpArch.Agent.Imposition.
-/

/-- BRIDGE THEOREM — Reversibility

    If CoreModel has no revision capability, safe withdrawal fails for the
    canonical failure-mode scenario (mistakeOccurred = true, harmIsPermanent = true).

    **Theorem shape:** ¬CoreHasRevision M → h_goal → False.
    **Proof strategy:** Project M via coreToWithdrawalScenario (hasReversibility = false),
    then delegate to safe_withdrawal_needs_reversibility. -/
theorem core_no_revision_violates_safe_withdrawal
    (M : CoreModel)
    (h_no_rev : ¬CoreHasRevision M)
    (h_goal : EpArch.Agent.SafeWithdrawalGoal
                ((coreToWithdrawalScenario M h_no_rev).mistakeOccurred = true)
                ((coreToWithdrawalScenario M h_no_rev).harmIsPermanent = true)) :
    False :=
  safe_withdrawal_needs_reversibility (coreToWithdrawalScenario M h_no_rev) rfl rfl h_goal

/-- BRIDGE THEOREM — Cheap Validator

    If CoreModel has no cheap validator, sound deposits fail for the
    canonical cost-overrun scenario (claimCost = budget + 1 > budget).

    **Theorem shape:** ¬CoreHasCheapValidator M → h_goal → False.
    **Proof strategy:** Project M via coreToDepositScenario (cost exceeds budget),
    then delegate to sound_deposits_need_cheap_validator. -/
theorem core_no_validator_violates_sound_deposits
    (M : CoreModel)
    (h_no_val : ¬CoreHasCheapValidator M)
    (budget : Nat)
    (h_goal : EpArch.Agent.SoundDepositsGoal
                (coreToDepositScenario M h_no_val budget).claimCost
                (coreToDepositScenario M h_no_val budget).budget) :
    False :=
  sound_deposits_need_cheap_validator (coreToDepositScenario M h_no_val budget) rfl h_goal

/-- BRIDGE THEOREM — Export Gate

    If CoreModel has no export gate, reliable export fails for the
    canonical silent-error scenario (observationCorrect = false, exportBlocked = false).

    **Theorem shape:** ¬CoreHasExportGate M → h_goal → False.
    **Proof strategy:** Project M via coreToExportScenario (observation incorrect, export unblocked),
    then delegate to reliable_export_needs_gate. -/
theorem core_no_gate_violates_reliable_export
    (M : CoreModel)
    (h_no_gate : ¬CoreHasExportGate M)
    (h_goal : EpArch.Agent.ReliableExportGoal
                ((coreToExportScenario M h_no_gate).observationCorrect = true)
                ((coreToExportScenario M h_no_gate).exportBlocked = true)) :
    False :=
  reliable_export_needs_gate (coreToExportScenario M h_no_gate) rfl h_goal

end


end EpArch.Mechanisms
