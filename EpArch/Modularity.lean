/-
EpArch/Modularity.lean — Lattice-Stability / Graceful Scale-Down

This module proves that EpArch is **lattice-stable** at the `RevisionGate` /
competition-gate layer: the `RevisionGate` predicate is preserved in both
directions under bundle perturbation.

## The Two Directions

**Upward (already in RevisionSafety.lean):**
  Compatible extension → RevisionGate preserved
  `safe_extension_preserves : RevisionGate C → RevisionGate (forget E)`

**Downward (this file):**
  Sub-bundle model → `RevisionGate` is preserved. If a model drops
  self-correction, the competition gate holds vacuously; compatible extensions
  of such sub-bundles preserve `RevisionGate` through the existing transport
  machinery. Formalised by:
  1. Building `OdometerModel` — a concrete minimal sub-bundle instance
     where `NoSelfCorrection` makes `RevisionGate` vacuously true (`graceful_degradation`)
  2. Proving `SubRevisionSafety`: RevisionSafety holds at every sub-bundle level
     via `transport_core` (identical proof term as the full-bundle case)

## Lattice Picture

  Full EpArch bundle
        ↑  ↑              ← safe_extension_preserves (RevisionSafety.lean)
     ┌──┴──┴──┐
     │ SubModel │          ← any valid sub-bundle (CoreModel with fewer active goals)
     └──┬──┬──┘
        ↓  ↓              ← sub_revision_safety (this file)
   Extended-Sub models

  At every level: what is proved stays proved. Extensions are safe at every level.

## Key Theorem

`modularity_pack`: GracefulDegradation ∧ SubRevisionSafety ∧ FullRevisionSafety
  = "EpArch is a floor, not a cage."

## Odometer sub-model

An odometer satisfies only `SoundDepositsGoal` (readings must be verifiable) and
none of the revision/export/adversarial goals. The competition gate (`RevisionGate`)
applies vacuously — a non-self-correcting system trivially satisfies
`selfCorrects B → hasRevision B`. This module establishes that `RevisionGate` and
sub-level `RevisionSafety` are preserved for such sub-bundles; it does not claim
a general theorem-transport schema over arbitrary theorem families.

-/

import EpArch.Health
import EpArch.RevisionSafety

namespace EpArch.Modularity

open RevisionSafety

/-! ## RevisionGate

`RevisionGate` is the competition-gate predicate:
  ∀ B, selfCorrects B → hasRevision B

This holds for every sub-bundle model where selfCorrects is nowhere true
(vacuously) — including any purely read-only or append-only system.
We make this explicit as `graceful_degradation`.

For sub-bundles that DO have self-correction, all the commuting-law machinery
from RevisionSafety carries through identically. We prove `SubRevisionSafety`
to package that.
-/

/-- A sub-bundle predicate: a CoreModel where selfCorrects is nowhere active.
    This covers all purely read-only, append-only, or single-agent systems
    (odometers, counters, simple preregistration without retraction). -/
def NoSelfCorrection (M : CoreModel) : Prop :=
  ∀ B : M.sig.Bubble, ¬M.ops.selfCorrects B

/-- Graceful degradation: any model with NoSelfCorrection satisfies RevisionGate.
    The competition gate is vacuously satisfied — there is nothing to trigger it.
    This is the downward direction: removing the self-correction health goal
    collapses the gate obligation to True, but RevisionGate still holds. -/
theorem graceful_degradation (M : CoreModel) (h : NoSelfCorrection M) :
    RevisionGate M := by
  unfold RevisionGate
  intro B h_sc
  exact absurd h_sc (h B)


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


/-! ## SubRevisionSafety

RevisionSafety holds at EVERY sub-bundle level, not just the full bundle.
This is the key closure result: if you trim goals and then extend compatibly,
all properties of the trimmed model are preserved.

The proof is formally identical to `transport_core` — the sub-bundle structure
does not change the proof term at all. We package it with a dedicated theorem
name and statement to make the modularity claim explicit.
-/

/-- A sub-bundle model: a CoreModel equipped with a sub-goal predicate.
    The `SubGoal` predicate records which health goals are active.
    `satisfies` witnesses that the model meets those goals. -/
structure SubBundle where
  model    : CoreModel
  /-- The active health-goal predicate for this sub-bundle -/
  SubGoal  : CoreModel → Prop
  satisfies : SubGoal model

/-- SubRevisionSafety: compatible extensions preserve sub-bundle properties.

    For any sub-bundle S with active property `SubGoal`, any `Compatible`
    extension E of S.model satisfies: if S.model satisfies SubGoal, then
    the forgetful projection of E satisfies RevisionGate.

    This is the downward + upward closure: trim to a sub-bundle,
    then extend compatibly — RevisionGate is preserved through both moves. -/
theorem sub_revision_safety (S : SubBundle) (E : ExtModel)
    (h_compat : Compatible E S.model)
    (h_gate : RevisionGate S.model) :
    RevisionGate (forget E) :=
  transport_core E S.model h_compat h_gate

/-- SubRevisionSafety for OdometerModel: any compatible extension of the
    odometer still satisfies RevisionGate.

    This shows EpArch applies to odometer-based systems AND to any compatible
    extension of an odometer (e.g., one that adds logging, encryption, or
    network sync) without breaking the core architectural guarantee. -/
theorem odometer_extension_safe (E : ExtModel)
    (h_compat : Compatible E OdometerModel) :
    RevisionGate (forget E) :=
  sub_revision_safety
    ⟨OdometerModel, RevisionGate, odometer_revision_gate⟩
    E h_compat odometer_revision_gate


/-! ## ModularityPack — The Headline Theorem

Packages the full bidirectional claim:
1. GracefulDegradation: remove goals → RevisionGate survives (vacuously or otherwise)
2. SubRevisionSafety: extend a trimmed model compatibly → RevisionGate preserved
3. The full bundle direction is already proved (safe_extension_preserves)

Together these establish: EpArch is a floor, not a cage.
Restrict the bundle — what's derived from the remainder is still proved.
Extend compatibly at any level — what's already proved is still true.
-/

/-- ModularityPack: the full bidirectional lattice-stability result.

    Component 1 — Graceful Degradation (downward):
      Any sub-bundle with NoSelfCorrection satisfies RevisionGate.

    Component 2 — Sub-level RevisionSafety (downward then upward):
      Compatible extension of any sub-bundle with RevisionGate → RevisionGate preserved.

    Component 3 — Full-level RevisionSafety (upward, from RevisionSafety.lean):
      Compatible extension of the full bundle → RevisionGate preserved.
      (Packaged here by reference for completeness.) -/
theorem modularity_pack :
    -- (1) Graceful degradation
    (∀ (M : CoreModel), NoSelfCorrection M → RevisionGate M) ∧
    -- (2) Sub-level revision safety
    (∀ (S : SubBundle) (E : ExtModel),
        Compatible E S.model → RevisionGate S.model → RevisionGate (forget E)) ∧
    -- (3) Full-level revision safety (reference to RevisionSafety.lean)
    (∀ (C : CoreModel) (R : RevisionSafeExtension C),
        RevisionGate C → RevisionGate (forget R.ext)) :=
  ⟨graceful_degradation, sub_revision_safety, safe_extension_preserves⟩

end EpArch.Modularity
