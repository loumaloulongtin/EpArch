/-
EpArch.Mechanisms — Canonical Mechanism Predicates

This module defines the canonical mechanism predicates that health goals
force under agent constraints. These are the "what the system must have"
predicates that design-imposition theorems target.

This file consolidates predicates previously scattered across multiple files into:
1. Abstract mechanism predicates (Prop-level, for agent reasoning)
2. CoreModel mechanism predicates (for EpArch.Health integration)
3. CoreModel-indexed canonical counterexample witnesses and bridge theorems (Imposition wiring)

## Design

Mechanism predicates answer: "What capability does the system have?"
- NOT whether the capability is used correctly
- NOT the implementation details
- Just: does the mechanism exist?

Bridge theorems connect CoreModel capability-absence predicates to the Imposition necessity
results in EpArch.Agent.Imposition: each states that a CoreModel lacking capability X
cannot satisfy the corresponding architectural goal for the canonical failure-mode
scenario. Proofs delegate to the counterexample proofs in Imposition. The `coreToX`
functions instantiate the canonical scenario under a `¬CoreHasX M` hypothesis; they
do not derive scenario fields from CoreModel internals.

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

/-- CoreModel has export gate: at least one deposit is verifiable as truth at some bubble.

    `CoreOps` carries no dedicated export-gate primitive. This predicate captures
    the reachability of truth-verification (`ops.truth B d`) that an export gate
    would require — a system lacking any truth-verifiable deposit at any bubble
    cannot intercept incorrect observations at export boundaries. -/
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


/-! ## Canonical Failure-Mode Scenario Witnesses

Each function instantiates the canonical Imposition failure-mode scenario under a
`¬CoreHasX M` hypothesis. The `CoreModel` and its negated capability hypothesis are
parameters for indexing purposes; the scenario fields are not computed from CoreModel
operations. The functions witness that the `¬CoreHasX` shape matches the scenario
shape used by the corresponding Imposition counterexample theorem.
-/

section
open EpArch.Agent

/-- Canonical failure-mode scenario for a CoreModel without revision capability.
    Instantiates the withdrawal counterexample: mistakeOccurred = true,
    harmIsPermanent = true, hasReversibility = false. The `¬CoreHasRevision M`
    hypothesis indexes this instantiation to the CoreModel failure condition. -/
def coreToWithdrawalScenario (_M : CoreModel) (_h_no_rev : ¬CoreHasRevision _M) :
    WithdrawalScenario where
  mistakeOccurred  := true
  harmIsPermanent  := true
  hasReversibility := false
  no_rev_permanent := fun _ _ => rfl

/-- Canonical failure-mode scenario for a CoreModel without cheap validator.
    Instantiates the deposit counterexample: claimCost = budget + 1 > budget,
    hasValidator = false. The `¬CoreHasCheapValidator M` hypothesis indexes this
    instantiation to the CoreModel failure condition. -/
def coreToDepositScenario (_M : CoreModel) (_h_no_val : ¬CoreHasCheapValidator _M)
    (budget : Nat) : DepositScenario :=
  deposit_counterexample budget

/-- Canonical failure-mode scenario for a CoreModel without export gate.
    Instantiates the export counterexample: observationCorrect = false,
    exportBlocked = false, hasGate = false. The `¬CoreHasExportGate M` hypothesis
    indexes this instantiation to the CoreModel failure condition. -/
def coreToExportScenario (_M : CoreModel) (_h_no_gate : ¬CoreHasExportGate _M) :
    ExportScenario :=
  export_counterexample


/-! ## CoreModel Bridge Theorems

These theorems connect the Imposition necessity results to the CoreModel. Each theorem
states that a CoreModel lacking capability X cannot satisfy the corresponding architectural
goal for the canonical failure-mode scenario. Proofs delegate to the genuine counterexample
proofs in EpArch.Agent.Imposition. The `coreToX` functions index the canonical scenario to
the CoreModel failure condition; they do not derive scenario fields from CoreModel internals.
-/

/-- BRIDGE THEOREM — Reversibility

    If CoreModel has no revision capability, safe withdrawal fails for the
    canonical failure-mode scenario (mistakeOccurred = true, harmIsPermanent = true).

    **Theorem shape:** ¬CoreHasRevision M → h_goal → False.
    **Proof strategy:** Instantiate the canonical withdrawal counterexample under the
    ¬CoreHasRevision hypothesis, then delegate to safe_withdrawal_needs_reversibility. -/
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
    **Proof strategy:** Instantiate the canonical deposit counterexample under the
    ¬CoreHasCheapValidator hypothesis, then delegate to sound_deposits_need_cheap_validator. -/
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
    **Proof strategy:** Instantiate the canonical export counterexample under the
    ¬CoreHasExportGate hypothesis, then delegate to reliable_export_needs_gate. -/
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
