/-
EpArch/Meta/LeanKernel/OdometerModel.lean — Odometer Sub-bundle

A concrete minimal EpArch sub-bundle witness.  An odometer satisfies only
`SoundDepositsGoal` (readings must be verifiable) and none of the
revision/export/adversarial goals.  The competition gate (`RevisionGate`)
applies vacuously — a non-self-correcting system trivially satisfies
`selfCorrects B → hasRevision B`.

This module establishes that `RevisionGate` and sub-level `RevisionSafety`
are preserved for such sub-bundles; it does not claim a general
theorem-transport schema over arbitrary theorem families.
-/

import EpArch.Meta.TheoremTransport

namespace EpArch.Meta.LeanKernel

open RevisionSafety
open EpArch.Meta.TheoremTransport

/-! ## OdometerModel — Concrete Minimal Sub-bundle

An odometer demonstrates that EpArch applies to systems with only one active
health goal (`SoundDepositsGoal`). All revision/export/adversarial goals are absent.
`OdometerModel` is a concrete `CoreModel` instance.

The model:
- One bubble (Nat representing cumulative count)
- One deposit type (Nat representing a reading)
- verification: reading ≤ current value is instantly verifiable (time = Unit)
- No self-correction: an odometer reading is not revisable
- No export: readings are local
- truth: reading does not exceed current count (`reading ≤ count`)

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

/-- Any compatible extension of the odometer still satisfies RevisionGate.

    This shows EpArch applies to odometer-based systems AND to any compatible
    extension of an odometer (e.g., one that adds logging, encryption, or
    network sync) without breaking the core architectural guarantee. -/
theorem odometer_extension_safe (E : ExtModel)
    (h_compat : Compatible E OdometerModel) :
    RevisionGate (forget E) :=
  sub_revision_safety
    ⟨OdometerModel, RevisionGate, odometer_revision_gate⟩
    E h_compat odometer_revision_gate

end EpArch.Meta.LeanKernel
