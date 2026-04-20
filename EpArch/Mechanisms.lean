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
corresponding Imposition necessity scenario." The `Imposition` scenario types
use `Bool` flags; `CoreOps` predicates (`hasRevision`, `truth`) are `Prop`.
This Bool↔Prop gap means scenario flags cannot be derived from CoreModel
operations, so bridge theorems call the canonical Imposition counterexamples
directly. The `M : CoreModel` and `_h_no_X` parameters scope each claim to
a specific CoreModel but are unused in the proof body.

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



/-! ## CoreModel Bridge Theorems

The `Imposition` scenario types use `Bool` flags; `CoreOps` predicates (`hasRevision`,
`truth`) are `Prop`. This Bool↔Prop gap means scenario flags cannot be derived from
CoreModel operations, so each bridge theorem calls the canonical Imposition
counterexample directly. The `M : CoreModel` and `_h_no_X` parameters appear in the
theoremtype to scope the claim to a specific CoreModel lacking capability X; they
do not appear in the proof body.
-/

section
open EpArch.Agent

/-- BRIDGE THEOREM — Reversibility

    A CoreModel lacking revision capability cannot satisfy SafeWithdrawalGoal
    for the canonical withdrawal counterexample.

    **Theorem shape:** ¬CoreHasRevision M → h_goal → False.
    **Note:** `withdrawal_counterexample` has `hasReversibility = false` by
    construction. `_h_no_rev` scopes this claim to CoreModels lacking revision
    but is unused in the proof: the Bool↔Prop gap prevents deriving the `Bool`
    flag from `M.ops.hasRevision B : Prop`. -/
theorem core_no_revision_violates_safe_withdrawal
    (M : CoreModel) (_h_no_rev : ¬CoreHasRevision M)
    (h_goal : EpArch.Agent.SafeWithdrawalGoal
                (withdrawal_counterexample.mistakeOccurred = true)
                (withdrawal_counterexample.harmIsPermanent = true)) :
    False :=
  safe_withdrawal_needs_reversibility withdrawal_counterexample rfl rfl h_goal

/-- BRIDGE THEOREM — Cheap Validator

    A CoreModel lacking a cheap validator cannot satisfy SoundDepositsGoal
    for the canonical cost-overrun scenario.

    **Theorem shape:** ¬CoreHasCheapValidator M → h_goal → False.
    **Note:** `DepositScenario` models numeric claim-cost pressure with no
    counterpart in `CoreOps`; `_h_no_val` scopes the theorem to CoreModels
    lacking the capability but does not appear in the arithmetic proof. -/
theorem core_no_validator_violates_sound_deposits
    (M : CoreModel) (_h_no_val : ¬CoreHasCheapValidator M) (budget : Nat)
    (h_goal : EpArch.Agent.SoundDepositsGoal
                (deposit_counterexample budget).claimCost
                (deposit_counterexample budget).budget) :
    False :=
  sound_deposits_need_cheap_validator (deposit_counterexample budget) rfl h_goal

/-- BRIDGE THEOREM — Export Gate

    A CoreModel lacking truth-verifiable deposits cannot satisfy
    ReliableExportGoal for the canonical export counterexample.

    **Theorem shape:** ¬CoreHasExportGate M → h_goal → False.
    **Note:** `export_counterexample` has `hasGate = false` by construction.
    `_h_no_gate` scopes this claim to CoreModels lacking export gates
    but is unused in the proof: the Bool↔Prop gap prevents deriving the `Bool`
    flag from `M.ops.truth B d : Prop`. -/
theorem core_no_gate_violates_reliable_export
    (M : CoreModel) (_h_no_gate : ¬CoreHasExportGate M)
    (h_goal : EpArch.Agent.ReliableExportGoal
                (export_counterexample.observationCorrect = true)
                (export_counterexample.exportBlocked = true)) :
    False :=
  reliable_export_needs_gate export_counterexample rfl h_goal

end


end EpArch.Mechanisms
