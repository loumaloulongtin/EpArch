/-
EpArch/Meta/LeanKernel/OdometerModel.lean — Odometer-Inspired Minimal Witness

A concrete minimal EpArch witness inspired by the picture of an odometer as a
monotone local readout.  This is a stylized abstraction, not a literal model of
real odometer hardware or all odometer-relevant behaviors.

The purpose of the module is narrow: it exhibits a sub-bundle in which only
`SoundDepositsGoal` is active, while revision/export/adversarial goals are absent.
The competition gate (`RevisionGate`) therefore holds vacuously, since the model
has no self-correction and no revision capability.

This module establishes:
- The exact goal-stance profile (which goals hold, which fail, and why)
- A typed bundle theorem (`odometer_is_minimal_goal_witness`) naming that profile
- Preservation of `RevisionGate` and sub-level `RevisionSafety` under compatible extensions
- A staleness structure distinguishing *true-but-superseded* deposits from
  *false* ones: the ledger is append-only; readings become stale, never false.

It does not claim a general theorem-transport schema over arbitrary theorem families,
and it does not claim to capture the full mechanics of real odometers.
-/

import EpArch.Meta.TheoremTransport

namespace EpArch.Meta.LeanKernel

open RevisionSafety
open EpArch.Meta.TheoremTransport

/-! ## OdometerModel — Concrete Minimal Sub-bundle

`OdometerModel` is a concrete minimal witness for the case where only
`SoundDepositsGoal` is active.  It is motivated by the picture of an odometer as
a monotone readable counter, but it should be read as a toy abstraction rather
than as a literal device model.

The model keeps only the structure needed for the targeted witness:
- one bubble (`Nat`) representing a cumulative local state
- one deposit type (`Nat`) representing a displayed reading
- trivial verification within effective time
- no revision capability
- no export structure
- truth: the simple monotonic condition `reading ≤ count`

Goal-stance profile:
| Goal                | Holds? | Reason                                               |
|---------------------|--------|------------------------------------------------------|
| SoundDepositsGoal   | yes    | every true reading is instantly verifiable           |
| SelfCorrectionGoal  | yes    | vacuously (selfCorrects = False, premise never true) |
| CorrigibleLedgerGoal| NO     | no bubble has hasRevision                            |
| SafeWithdrawalGoal  | NO     | submit always True but hasRevision always False      |
| ReliableExportGoal  | NO     | truth is local (reading ≤ B); cross-bubble not held  |

Note on truth vs. currency: `truth B d = (d ≤ B)` makes all past readings
permanently true — once a milestone is reached it stays reached forever.
This is distinct from *currency* (`d = B`: the present count is the live
deposit).  The staleness section below (`isCurrentOdometerReading`,
`isStaleOdometerReading`) makes this structure machine-checked.
-/

/-- The concrete OdometerModel. -/
def OdometerModel : CoreModel where
  sig := {
    Agent  := Unit                 -- single operator (driver)
    Claim  := Nat                  -- the claimed reading
    Bubble := Nat                  -- bubble = current odometer count
    Time   := Unit                 -- verification is instantaneous
    Deposit := Nat                 -- a deposit = a recorded reading
    Header := Unit                 -- no structured header needed
  }
  ops := {
    -- A reading is "true" if it does not exceed the current count
    truth          := fun count reading => reading ≤ count
    -- Every reading is observable (visible on the dashboard)
    obs            := fun _ => True
    -- Verification is always possible (comparison is O(1))
    verifyWithin   := fun _ _ _ => True
    -- Effective time is Unit (unlimited / instantaneous)
    effectiveTime  := fun _ => ()
    -- Submit: always succeeds for any reading
    submit         := fun _ _ _ => True
    -- Revise: odometers don't revise — vacuously false
    revise         := fun _ _ _ => False
    -- deposit_header: trivial, returns Unit
    deposit_header := fun _ => ()
    -- hasRevision: no bubble has revision capability
    hasRevision    := fun _ => False
    -- selfCorrects: no bubble self-corrects
    selfCorrects   := fun _ => False
  }
  hasBubble := ⟨0⟩

/-- OdometerModel has NoSelfCorrection. -/
theorem odometer_no_self_correction : NoSelfCorrection OdometerModel :=
  fun _ h_sc => h_sc

/-- OdometerModel satisfies RevisionGate (vacuously). -/
theorem odometer_revision_gate : RevisionGate OdometerModel :=
  graceful_degradation OdometerModel odometer_no_self_correction

/-- OdometerModel satisfies SoundDepositsGoal:
    every true reading (≤ current count) is verifiable within effective time. -/
theorem odometer_sound_deposits : SoundDepositsGoal OdometerModel :=
  fun _ _ _ => True.intro

/-- OdometerModel does NOT satisfy CorrigibleLedgerGoal:
    no bubble has revision capability. -/
theorem odometer_not_corrigible : ¬CorrigibleLedgerGoal OdometerModel :=
  fun ⟨⟨_, h_rev⟩, _⟩ => h_rev

/-- OdometerModel does NOT satisfy SafeWithdrawalGoal:
    `submit` always succeeds (True) but `hasRevision` is always False,
    so the implication `submit → hasRevision` fails for every reading.

    The failure mode this captures is the **broken odometer**: if the
    measurement mechanism fails at count B and is later repaired, it silently
    resumes from B — all distance covered during the failure is omitted.  The
    submitted reading is false (it understates true mileage), but the system
    has no mechanism to detect or correct this.  `SafeWithdrawalGoal` requires
    any submitting bubble to have revision capability; this model provides none.

    Note: this is strictly different from staleness.  A stale deposit (d < B)
    is *true* — the milestone was reached.  A post-breakage deposit is *false*
    — the mileage was NOT accumulated.  Revision is needed only for the latter.
    The current model is `¬SafeWithdrawalGoal` precisely because it cannot
    distinguish the two cases: submit is unconditional. -/
theorem odometer_not_safe_withdrawal : ¬SafeWithdrawalGoal OdometerModel :=
  fun h => h () Nat.zero Nat.zero True.intro

/-- OdometerModel does NOT satisfy ReliableExportGoal:
    truth is local (`reading ≤ count`); there is no cross-bubble guarantee.
    Counterexample: B = 5, B' = 10, d = 7.
    d > B (not true in B) but d ≤ B' (true in B'), and hasRevision B' = False. -/
theorem odometer_not_reliable_export : ¬ReliableExportGoal OdometerModel := by
  -- Expose concrete Nat types so that `decide` can reduce the inequalities.
  show (∀ (B B' d : Nat), ¬(d ≤ B) → ¬(d ≤ B') ∨ False) → False
  intro h
  have h5 := h 5 10 7 (by decide)
  cases h5 with
  | inl h1 => exact h1 (by decide)
  | inr h2 => exact h2

/-- OdometerModel satisfies SelfCorrectionGoal vacuously:
    `selfCorrects = False` so the premise `selfCorrects B` is never true. -/
theorem odometer_self_correction_vacuous : SelfCorrectionGoal OdometerModel :=
  fun _ h_sc => h_sc.elim

/-! ## Staleness: Truth vs. Currency

An odometer deposit can be **true** (the milestone was historically reached)
without being **current** (the present live reading).  These notions come apart
as soon as the count advances: once the bubble moves past d, deposit d remains
permanently true but is no longer the authoritative claim.

`isCurrentOdometerReading B d` — d equals the present count (the live deposit)
`isStaleOdometerReading B d`   — d was reached but the count has since advanced

Key structural property: the ledger is monotone-append.  Nothing is ever
retracted; readings only become stale, never false.  This is WHY revision is
absent in the base model: there is nothing to correct.  The only possible
source of falsity is a broken measurement mechanism — a sensor failure that
submits a reading that was never actually reached.  That error cannot be
recovered without revision capability (see `odometer_not_safe_withdrawal`).

Consider any ledger where a fact is permanent but the stance toward it evolves.
The fact of a threshold crossed, a measurement taken, an event logged — these
are immutable entries; their truth value does not decay.  What *responds* to
that fact — the current assessment, the live authoritative claim built on top
of the historical record — is different in kind: it advances, may be revised,
and is the slot that requires revision capability if submitted incorrectly.

Both layers inhabit the same ledger; only the live claim is the target of safe
withdrawal.  Revision does not reach back into history — it corrects the
present stance.  This is exactly what the odometer makes precise: `truth B d`
is permanent once true; `isCurrentOdometerReading B d` is transient; and
`¬SafeWithdrawalGoal` names the risk that arises when the present claim has
no correction mechanism behind it. -/

/-- A deposit equals the present bubble count: the live, authoritative reading. -/
def isCurrentOdometerReading (B d : Nat) : Prop := d = B

/-- A deposit was true in the past but the count has since advanced: stale
    but permanently historically true.  Staleness ≠ falsity. -/
def isStaleOdometerReading (B d : Nat) : Prop := d < B

/-- Stale readings remain forever true: a milestone reached stays reached.
    The odometer ledger is append-only; no deposit ever becomes false. -/
theorem odometer_stale_remains_true (B d : Nat) (h : isStaleOdometerReading B d) :
    OdometerModel.ops.truth B d := by
  unfold isStaleOdometerReading at h
  show d ≤ B
  exact Nat.le_of_lt h

/-- Current and stale are mutually exclusive: no deposit is simultaneously
    the live reading and a superseded past entry. -/
theorem odometer_current_not_stale (B d : Nat) :
    ¬(isCurrentOdometerReading B d ∧ isStaleOdometerReading B d) := by
  unfold isCurrentOdometerReading isStaleOdometerReading
  intro ⟨heq, hlt⟩
  rw [heq] at hlt
  exact Nat.lt_irrefl B hlt

/-- The ledger grows strictly at every tick: the previous current reading
    becomes stale and a new authoritative deposit is installed. -/
theorem odometer_ledger_grows (B : Nat) :
    isStaleOdometerReading (B + 1) B ∧ isCurrentOdometerReading (B + 1) (B + 1) := by
  unfold isStaleOdometerReading isCurrentOdometerReading
  exact ⟨Nat.lt_succ_self B, rfl⟩

/-- Truth is strictly weaker than currency: for any B > 0 there exists a
    deposit that is true (historically reached) but not current (not the live
    reading).  The ledger always contains more than the present claim alone. -/
theorem odometer_truth_strictly_weaker_than_currency (B : Nat) (hB : 0 < B) :
    ∃ d : Nat, OdometerModel.ops.truth B d ∧ ¬isCurrentOdometerReading B d := by
  refine ⟨0, ?_, ?_⟩
  · show (0 : Nat) ≤ B
    exact Nat.zero_le B
  · unfold isCurrentOdometerReading
    intro h
    rw [h] at hB
    exact Nat.lt_irrefl B hB

/-! ## Typed Goal-Stance Bundle -/

/-- `odometer_is_minimal_goal_witness`: the complete typed goal-stance profile.

    This is the "EpArch profile" for the odometer-inspired minimal witness:
    exactly `SoundDepositsGoal` and (vacuous) `SelfCorrectionGoal` hold;
    the three revision/export/corrigibility goals are explicitly absent.

    This bundles all five goal stances into a single named theorem so the
    profile is machine-checked as a unit rather than just narrated. -/
theorem odometer_is_minimal_goal_witness :
    SoundDepositsGoal OdometerModel ∧
    SelfCorrectionGoal OdometerModel ∧
    ¬CorrigibleLedgerGoal OdometerModel ∧
    ¬SafeWithdrawalGoal OdometerModel ∧
    ¬ReliableExportGoal OdometerModel :=
  ⟨odometer_sound_deposits,
   odometer_self_correction_vacuous,
   odometer_not_corrigible,
   odometer_not_safe_withdrawal,
   odometer_not_reliable_export⟩

/-- Any compatible extension of the odometer still satisfies RevisionGate.

    This shows that the minimal witness remains safe under compatible extensions
    of the same abstract pattern (for example, extensions that add bookkeeping or
    additional local structure) without changing the core no-revision profile. -/
theorem odometer_extension_safe (E : ExtModel)
    (h_compat : Compatible E OdometerModel) :
    RevisionGate (forget E) :=
  sub_revision_safety
    ⟨OdometerModel, RevisionGate, odometer_revision_gate⟩
    E h_compat odometer_revision_gate

end EpArch.Meta.LeanKernel
