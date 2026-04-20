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
corresponding architectural goal." Two theorems use a `coreToX` projection into
an `Imposition` scenario type (reversibility, cheap validator). The third — reliable
export — bridges directly from `Health.ReliableExportGoal M`: since export is not a
bank primitive (step 15), the gate is truth-verification plus revision capability at
the receiving bubble, both already in `CoreOps`.

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


/-! ## CoreModel Scenario Projections

Two `coreToX` functions embed a `CoreModel` into the corresponding `Imposition`
scenario type. The third mechanism (reliable export) uses `Health.ReliableExportGoal M`
directly: since export is not a bank primitive (step 15), the relevant gate is
truth-verification (`ops.truth`) plus revision capability (`ops.hasRevision`) at the
receiving bubble — both already in `CoreOps`, no separate gate predicate needed.
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

/-! ## CoreModel Bridge Theorems

The first two bridge theorems project `M : CoreModel` via `coreToX`, then delegate
to the Imposition necessity theorem. The third — reliable export — applies
`Health.ReliableExportGoal M` directly via a case split, with all three witnesses
(`h_false`, `h_true`, `h_no_rev`) load-bearing.
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
    (stated over `validatorCost`) under the projected deposit scenario.

    **Theorem shape:** ¬CoreHasCheapValidator M → h_goal → False.
    **Proof strategy:** project M via `coreToDepositScenario`; pass `h_no_val`
    directly as `¬(coreToDepositScenario M budget).hasValidator` (definitionally equal).
    `sound_deposits_need_cheap_validator` then uses `h_no_val` via `no_validator_full_cost`
    to equate `validatorCost` to `claimCost`, and closes by `prp_pressure`. -/
theorem core_no_validator_violates_sound_deposits
    (M : CoreModel) (h_no_val : ¬CoreHasCheapValidator M) (budget : Nat)
    (h_goal : EpArch.Agent.SoundDepositsGoal
                (coreToDepositScenario M budget).validatorCost
                (coreToDepositScenario M budget).budget) :
    False :=
  sound_deposits_need_cheap_validator (coreToDepositScenario M budget) h_no_val h_goal

/-- BRIDGE THEOREM — Reliable Export

    A CoreModel with a false-positive deposit — true in B' but false in B, with B'
    lacking revision capability — cannot satisfy `Health.ReliableExportGoal`.

    Uses `EpArch.ReliableExportGoal M` directly (Health.lean). Since export is not
    a bank primitive (step 15), the gate is truth-verification plus revision capability
    at the receiving bubble. Both are already in `CoreOps`; no separate gate predicate
    in `CoreOps` is needed or appropriate.

    **Theorem shape:** ¬truth B d ∧ truth B' d ∧ ¬hasRevision B' → ReliableExportGoal M → False.
    **Proof strategy:** apply h_goal to the witnesses; case-split on the disjunction;
    each branch contradicts one of the explicit witness hypotheses. -/
theorem core_false_positive_violates_reliable_export
    (M : CoreModel)
    (B B' : M.sig.Bubble) (d : M.sig.Deposit)
    (h_false  : ¬M.ops.truth B d)
    (h_true   : M.ops.truth B' d)
    (h_no_rev : ¬M.ops.hasRevision B')
    (h_goal   : EpArch.ReliableExportGoal M) : False := by
  -- ReliableExportGoal says: ¬truth B d → ¬truth B' d ∨ hasRevision B'
  have h_disj := h_goal B B' d h_false
  -- Case split on the disjunction
  cases h_disj with
  | inl h_false' => exact h_false' h_true
  | inr h_rev    => exact h_no_rev h_rev

end


end EpArch.Mechanisms
