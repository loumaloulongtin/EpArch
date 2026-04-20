/-
EpArch.Mechanisms — Canonical Mechanism Predicates

This module defines the canonical mechanism predicates that health goals
force under agent constraints. These are the "what the system must have"
predicates that design-imposition theorems target.

This file consolidates predicates previously scattered across multiple files into:
1. CoreModel mechanism predicates (for EpArch.Health integration)
2. CoreModel bridge theorems (Imposition wiring)

## Design

Mechanism predicates answer: "What capability does the system have?"
- NOT whether the capability is used correctly
- NOT the implementation details
- Just: does the mechanism exist?

Bridge theorems state: "A CoreModel lacking capability X cannot satisfy the
corresponding Imposition necessity scenario." Each bridge theorem uses a
`coreToX` projection that sets `hasReversibility := CoreHasRevision M` (etc.),
so the `h_no_X` hypothesis is genuinely used. The `Imposition` scenario flags
are `Prop`, matching `CoreOps` predicate types.

-/

import EpArch.Basic
import EpArch.Semantics.RevisionSafety
import EpArch.Health
import EpArch.Agent.Imposition

namespace EpArch.Mechanisms

open EpArch.RevisionSafety

universe u

/-! ## CoreModel Mechanism Predicates

Predicates over `CoreModel` and `CoreOps` that name the structural
capabilities the Imposition necessity theorems require.
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



/-! ## CoreModel Scenario Projections

Each `coreToX` function embeds a `CoreModel` into the corresponding `Imposition`
scenario type by setting the capability flag to the CoreModel predicate. With
`Imposition` scenario flags now `Prop` (matching `CoreOps` predicate types),
the assignment is direct.
-/

section
open EpArch.Agent

/-- Project a CoreModel into a WithdrawalScenario.
    `hasReversibility` is `CoreHasRevision M`, so `¬CoreHasRevision M` is
    definitionally `¬(coreToWithdrawalScenario M).hasReversibility`. -/
def coreToWithdrawalScenario (M : CoreModel) : WithdrawalScenario where
  mistakeOccurred  := true
  harmIsPermanent  := true
  hasReversibility := CoreHasRevision M
  no_rev_permanent := fun _ _ => rfl

/-- Project a CoreModel into a DepositScenario.
    `hasValidator` is `CoreHasCheapValidator M`, so `¬CoreHasCheapValidator M` is
    definitionally `¬(coreToDepositScenario M budget).hasValidator`. -/
def coreToDepositScenario (M : CoreModel) (budget : Nat) : DepositScenario where
  claimCost             := budget + 1
  budget                := budget
  validatorCost         := budget + 1
  hasValidator          := CoreHasCheapValidator M
  prp_pressure          := Nat.lt_succ_self budget
  no_validator_full_cost := fun _ => rfl

/-- Project a CoreModel into an ExportScenario.
    `hasGate` is `CoreHasExportGate M`, so `¬CoreHasExportGate M` is
    definitionally `¬(coreToExportScenario M).hasGate`. -/
def coreToExportScenario (M : CoreModel) : ExportScenario where
  observationCorrect := false
  exportBlocked      := false
  hasGate            := CoreHasExportGate M
  fallible           := rfl
  no_gate_exports    := fun _ => rfl

/-! ## CoreModel Bridge Theorems

Each bridge theorem projects `M : CoreModel` via `coreToX`, then delegates to
the Imposition necessity theorem. The `h_no_X` hypothesis is genuinely used:
`h_no_rev : ¬CoreHasRevision M` is definitionally `¬(coreToWithdrawalScenario M).hasReversibility`,
so it discharges the corresponding argument of `safe_withdrawal_needs_reversibility`.
-/

/-- BRIDGE THEOREM — Reversibility

    A CoreModel lacking revision capability cannot satisfy SafeWithdrawalGoal
    under the projected withdrawal scenario.

    **Theorem shape:** ¬CoreHasRevision M → h_goal → False.
    **Proof strategy:** project M via `coreToWithdrawalScenario`; pass `h_no_rev`
    directly as `¬(coreToWithdrawalScenario M).hasReversibility` (definitionally equal). -/
theorem core_no_revision_violates_safe_withdrawal
    (M : CoreModel) (h_no_rev : ¬CoreHasRevision M)
    (h_goal : EpArch.Agent.SafeWithdrawalGoal
                ((coreToWithdrawalScenario M).mistakeOccurred = true)
                ((coreToWithdrawalScenario M).harmIsPermanent = true)) :
    False :=
  safe_withdrawal_needs_reversibility (coreToWithdrawalScenario M) rfl h_no_rev h_goal

/-- BRIDGE THEOREM — Cheap Validator

    A CoreModel lacking a cheap validator cannot satisfy SoundDepositsGoal
    under the projected deposit scenario.

    **Theorem shape:** ¬CoreHasCheapValidator M → h_goal → False.
    **Proof strategy:** project M via `coreToDepositScenario`; pass `h_no_val`
    directly as `¬(coreToDepositScenario M budget).hasValidator` (definitionally equal).
    The contradiction in `sound_deposits_need_cheap_validator` is arithmetic
    (`prp_pressure` vs `SoundDepositsGoal`); `h_no_val` is forwarded but unused there. -/
theorem core_no_validator_violates_sound_deposits
    (M : CoreModel) (h_no_val : ¬CoreHasCheapValidator M) (budget : Nat)
    (h_goal : EpArch.Agent.SoundDepositsGoal
                (coreToDepositScenario M budget).claimCost
                (coreToDepositScenario M budget).budget) :
    False :=
  sound_deposits_need_cheap_validator (coreToDepositScenario M budget) h_no_val h_goal

/-- BRIDGE THEOREM — Export Gate

    A CoreModel lacking truth-verifiable deposits cannot satisfy ReliableExportGoal
    under the projected export scenario.

    **Theorem shape:** ¬CoreHasExportGate M → h_goal → False.
    **Proof strategy:** project M via `coreToExportScenario`; pass `h_no_gate`
    directly as `¬(coreToExportScenario M).hasGate` (definitionally equal). -/
theorem core_no_gate_violates_reliable_export
    (M : CoreModel) (h_no_gate : ¬CoreHasExportGate M)
    (h_goal : EpArch.Agent.ReliableExportGoal
                ((coreToExportScenario M).observationCorrect = true)
                ((coreToExportScenario M).exportBlocked = true)) :
    False :=
  reliable_export_needs_gate (coreToExportScenario M) h_no_gate h_goal

end


end EpArch.Mechanisms
