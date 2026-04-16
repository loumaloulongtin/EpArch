/-
EpArch.Meta.TheoremTransport — Generic Theorem Transport Schema

This module formalizes the modularity story from DOCS/MODULARITY.md Tier 3 and
closes the gap described there: it proves that every `CoreModel`-level health goal
predicate is **transport-safe** under compatible extensions.

## What "transport-safe" means

A predicate `P : CoreModel → Prop` is transport-safe if:

    Compatible E C → P C → P (forget E)

That is: if `C` satisfies `P`, then any compatible extension of `C` (projected back
to the core via `forget`) also satisfies `P`. This is the upward direction of
lattice-stability for the full health-goal layer.

## Coverage

### Fully transport-safe with `Compatible` (∀-predicates)

| Predicate | Operations used | Transport theorem |
|---|---|---|
| `RevisionGate` / `SelfCorrectionGoal` | `selfCorrects`, `hasRevision` | `transport_self_correction` (= `transport_core`) |
| `SafeWithdrawalGoal` | `submit`, `hasRevision` | `transport_safe_withdrawal` |
| `ReliableExportGoal` | `truth`, `hasRevision` | `transport_reliable_export` |
| `SoundDepositsGoal` | `truth`, `verifyWithin`, `effectiveTime` | `transport_sound_deposits` |
| `CorrigibleLedgerGoal` (universal part) | `hasRevision`, `revise`, `truth` | `transport_corrigible_universal` |

### Requires `SurjectiveCompatible` (∃-predicates)

| Predicate | Operations used | Transport theorem |
|---|---|---|
| `CorrigibleLedgerGoal` (full, incl. ∃ part) | `hasRevision`, `revise`, `truth` | `transport_corrigible_ledger` |

## Disabled Operations

`VacuousOp_*` predicates formally define what it means for an operation to be
"disabled" in a model (always false / always trivially satisfied). These correspond
to the "disabling a constraint or health goal" story in DOCS/MODULARITY.md.

## Headline theorem

`health_goal_transport_pack` packages all five ∀-transport results together.

-/

import EpArch.Health

namespace EpArch.Meta.TheoremTransport

open RevisionSafety

universe u

/-! ## 2. Surjective Compatible

`Compatible` requires commuting laws but not surjectivity of the projection maps.
For ∀-predicates (like RevisionGate, SafeWithdrawalGoal, etc.), this is enough.
For ∃-predicates (like the existence component of CorrigibleLedgerGoal), we need
to pull back a witness from C to E, which requires surjectivity of `πBubble`.
-/

/-- Surjective compatible extension: extends Compatible with surjectivity of πBubble
    and πDeposit, enabling transport of ∃-predicates. -/
structure SurjectiveCompatible (E : ExtModel) (C : CoreModel) extends Compatible E C where
  /-- Every C-bubble has a preimage in E -/
  bubbleSurj : ∀ (B_C : C.sig.Bubble), ∃ (B_E : E.sig.Bubble), toCompatible.πBubble B_E = B_C
  /-- Every C-deposit has a preimage in E -/
  depositSurj : ∀ (d_C : C.sig.Deposit), ∃ (d_E : E.sig.Deposit), toCompatible.πDeposit d_E = d_C


/-! ## 3. Transport Theorems for Health Goals (∀-predicates)

Each theorem uses only the commuting laws relevant to its operation mask. -/

/-- Transport: `SafeWithdrawalGoal` is preserved by compatible extensions.

    Uses: `submit_comm`, `hasRevision_comm`.
    Statement: if submissions require revision capability in C, they still do in forget E. -/
theorem transport_safe_withdrawal (E : ExtModel) (C : CoreModel) (h : Compatible E C)
    (h_goal : SafeWithdrawalGoal C) : SafeWithdrawalGoal (forget E) := by
  intro a_E B_E d_E h_submit_E
  -- Transfer submit to C
  have h_submit_C := (h.submit_comm a_E B_E d_E).mp h_submit_E
  -- Apply goal at C
  have h_rev_C := h_goal (h.πAgent a_E) (h.πBubble B_E) (h.πDeposit d_E) h_submit_C
  -- Transfer hasRevision back to E
  exact (h.hasRevision_comm B_E).mpr h_rev_C

/-- Transport: `ReliableExportGoal` is preserved by compatible extensions.

    Uses: `truth_comm`, `hasRevision_comm`.
    Statement: false-in-B deposits are still false-or-revisable across boundaries in forget E. -/
theorem transport_reliable_export (E : ExtModel) (C : CoreModel) (h : Compatible E C)
    (h_goal : ReliableExportGoal C) : ReliableExportGoal (forget E) := by
  intro B_E B'_E d_E h_not_truth_E
  -- Transfer ¬truth to C
  have h_not_truth_C : ¬C.ops.truth (h.πBubble B_E) (h.πDeposit d_E) :=
    fun h_tc => h_not_truth_E ((h.truth_comm B_E d_E).mpr h_tc)
  -- Apply goal at C
  cases h_goal (h.πBubble B_E) (h.πBubble B'_E) (h.πDeposit d_E) h_not_truth_C with
  | inl h_not_truth_C' =>
    exact Or.inl (fun h_te => h_not_truth_C' ((h.truth_comm B'_E d_E).mp h_te))
  | inr h_rev_C =>
    exact Or.inr ((h.hasRevision_comm B'_E).mpr h_rev_C)

/-- Transport: `SoundDepositsGoal` is preserved by compatible extensions.

    Uses: `truth_comm`, `verifyWithin_comm`, `effectiveTime_comm`.
    Statement: verifiable-within-budget deposits remain so after extension. -/
theorem transport_sound_deposits (E : ExtModel) (C : CoreModel) (h : Compatible E C)
    (h_goal : SoundDepositsGoal C) : SoundDepositsGoal (forget E) := by
  intro B_E d_E h_truth_E
  -- Transfer truth to C
  have h_truth_C := (h.truth_comm B_E d_E).mp h_truth_E
  -- Apply goal: verifyWithin at C's effectiveTime
  have h_verify_C := h_goal (h.πBubble B_E) (h.πDeposit d_E) h_truth_C
  -- Rewrite: C.effectiveTime (πBubble B_E) = πTime (E.effectiveTime B_E)
  rw [← h.effectiveTime_comm B_E] at h_verify_C
  -- Transfer verifyWithin back: h_verify_C uses πTime (E.effectiveTime B_E)
  exact (h.verifyWithin_comm B_E d_E (E.ops.effectiveTime B_E)).mpr h_verify_C

/-- Transport: `SelfCorrectionGoal` is preserved by compatible extensions.

    `SelfCorrectionGoal` is definitionally equal to `RevisionGate`, so
    `transport_core` from `RevisionSafety` applies directly.

    Uses: `selfCorrects_comm`, `hasRevision_comm`. -/
theorem transport_self_correction (E : ExtModel) (C : CoreModel) (h : Compatible E C)
    (h_goal : SelfCorrectionGoal C) : SelfCorrectionGoal (forget E) :=
  transport_core E C h h_goal

/-- Transport: universal part of `CorrigibleLedgerGoal` (revisions produce truths).

    The existence component (∃ B, hasRevision B) requires surjectivity (see below).
    This theorem handles the universal part with plain `Compatible`.

    Uses: `hasRevision_comm`, `revise_comm`, `truth_comm`. -/
theorem transport_corrigible_universal (E : ExtModel) (C : CoreModel) (h : Compatible E C)
    (h_goal : CorrigibleLedgerGoal C) :
    ∀ B_E : (forget E).sig.Bubble, (forget E).ops.hasRevision B_E →
    ∀ d_E d'_E : (forget E).sig.Deposit,
    (forget E).ops.revise B_E d_E d'_E → (forget E).ops.truth B_E d'_E := by
  intro B_E h_rev_E d_E d'_E h_revise_E
  have h_rev_C    := (h.hasRevision_comm B_E).mp h_rev_E
  have h_revise_C := (h.revise_comm B_E d_E d'_E).mp h_revise_E
  have h_truth_C  := h_goal.2 (h.πBubble B_E) h_rev_C (h.πDeposit d_E) (h.πDeposit d'_E) h_revise_C
  exact (h.truth_comm B_E d'_E).mpr h_truth_C


/-! ## 4. Full CorrigibleLedgerGoal Transport (requires SurjectiveCompatible)

The existence component `∃ B, hasRevision B` cannot be transported with plain
Compatible because the projection πBubble goes E → C, and we need a preimage
in E for the C-bubble witnessing revision capability. Surjectivity provides this. -/

/-- Full transport: `CorrigibleLedgerGoal` preserved by surjective-compatible extensions.

    The existence component uses πBubble surjectivity to pull back the witness.
    The universal component uses `transport_corrigible_universal`. -/
theorem transport_corrigible_ledger (E : ExtModel) (C : CoreModel)
    (h : SurjectiveCompatible E C)
    (h_goal : CorrigibleLedgerGoal C) : CorrigibleLedgerGoal (forget E) :=
  let compat := h.toCompatible
  let ⟨B_C, h_rev_C⟩ := h_goal.1
  let ⟨B_E, h_proj⟩ := h.bubbleSurj B_C
  ⟨⟨B_E, (compat.hasRevision_comm B_E).mpr (h_proj ▸ h_rev_C)⟩,
   transport_corrigible_universal E C compat h_goal⟩


/-! ## 5. Disabled Operations (Vacuous Predicates)

Formally defines what it means for an operation to be "disabled" (vacuously false)
in a CoreModel. Corresponds to the disabling story in DOCS/MODULARITY.md Tiers 2–3. -/

/-- No bubble self-corrects. Disabling the self-correction operation. -/
def VacuousSelfCorrects (M : CoreModel) : Prop :=
  ∀ B : M.sig.Bubble, ¬M.ops.selfCorrects B

/-- No bubble has revision capability. Disabling the revision operation. -/
def VacuousHasRevision (M : CoreModel) : Prop :=
  ∀ B : M.sig.Bubble, ¬M.ops.hasRevision B

/-- No revision transition fires. Disabling the revise operation. -/
def VacuousRevise (M : CoreModel) : Prop :=
  ∀ (B : M.sig.Bubble) (d d' : M.sig.Deposit), ¬M.ops.revise B d d'

/-- No submission fires. Disabling the submit operation. -/
def VacuousSubmit (M : CoreModel) : Prop :=
  ∀ (a : M.sig.Agent) (B : M.sig.Bubble) (d : M.sig.Deposit), ¬M.ops.submit a B d

/-- Nothing is true in any bubble. Disabling the truth relation. -/
def VacuousTruth (M : CoreModel) : Prop :=
  ∀ (B : M.sig.Bubble) (d : M.sig.Deposit), ¬M.ops.truth B d

/-- Abbreviation: NoSelfCorrection = VacuousSelfCorrects, used in modularity theorems. -/
abbrev NoSelfCorrection (M : CoreModel) : Prop := VacuousSelfCorrects M

/-- Graceful degradation: any model with NoSelfCorrection satisfies RevisionGate.
    The competition gate is vacuously satisfied — there is nothing to trigger it. -/
theorem graceful_degradation (M : CoreModel) (h : NoSelfCorrection M) : RevisionGate M := by
  unfold RevisionGate
  intro B h_sc
  exact absurd h_sc (h B)


/-! ## 6. Consequences of Disabling Operations -/

/-- Disabling self-correction → RevisionGate holds vacuously.
    (Refactored reference to graceful_degradation in EpArch.Modularity.) -/
theorem vacuous_selfCorrects_revision_gate (M : CoreModel)
    (h : VacuousSelfCorrects M) : RevisionGate M :=
  graceful_degradation M h

/-- Disabling revise + hasRevision → universal part of CorrigibleLedgerGoal holds vacuously. -/
theorem vacuous_revision_corrigible_universal (M : CoreModel)
    (h : VacuousHasRevision M) :
    ∀ B : M.sig.Bubble, M.ops.hasRevision B →
    ∀ d d' : M.sig.Deposit, M.ops.revise B d d' → M.ops.truth B d' :=
  fun B h_rev _ _ _ => absurd h_rev (h B)

/-- Disabling submit → SafeWithdrawalGoal holds vacuously. -/
theorem vacuous_submit_safe_withdrawal (M : CoreModel)
    (h : VacuousSubmit M) : SafeWithdrawalGoal M :=
  fun a B d h_submit => absurd h_submit (h a B d)

/-- Disabling truth → SoundDepositsGoal holds vacuously. -/
theorem vacuous_truth_sound_deposits (M : CoreModel)
    (h : VacuousTruth M) : SoundDepositsGoal M :=
  fun B d h_truth => absurd h_truth (h B d)

/-- Disabling truth → ReliableExportGoal holds vacuously. -/
theorem vacuous_truth_reliable_export (M : CoreModel)
    (h : VacuousTruth M) : ReliableExportGoal M :=
  fun _ B' d _ => Or.inl (h B' d)


/-! ## 7. Headline Theorem: Health Goal Transport Pack

Packages all five ∀-transport results into a single theorem that can be
cited as evidence that the health-goal layer is transport-safe.

The two key claims:
 (A) Every ∀-health-goal is preserved by any compatible extension.
 (B) CorrigibleLedgerGoal (full) is preserved by any surjective-compatible extension.
-/

/-- All ∀-health-goals are transport-safe under plain Compatible extension.

    This is the Tier 3 closure theorem from DOCS/MODULARITY.md:
    for any CoreModel C satisfying a health goal, any compatible extension
    E of C still satisfies that goal (via the forgetful projection). -/
theorem health_goal_transport_pack :
    -- (1) SelfCorrectionGoal / RevisionGate
    (∀ (E : ExtModel) (C : CoreModel), Compatible E C →
        SelfCorrectionGoal C → SelfCorrectionGoal (forget E)) ∧
    -- (2) SafeWithdrawalGoal
    (∀ (E : ExtModel) (C : CoreModel), Compatible E C →
        SafeWithdrawalGoal C → SafeWithdrawalGoal (forget E)) ∧
    -- (3) ReliableExportGoal
    (∀ (E : ExtModel) (C : CoreModel), Compatible E C →
        ReliableExportGoal C → ReliableExportGoal (forget E)) ∧
    -- (4) SoundDepositsGoal
    (∀ (E : ExtModel) (C : CoreModel), Compatible E C →
        SoundDepositsGoal C → SoundDepositsGoal (forget E)) ∧
    -- (5) CorrigibleLedgerGoal (universal part)
    (∀ (E : ExtModel) (C : CoreModel), Compatible E C →
        CorrigibleLedgerGoal C →
        ∀ B_E : (forget E).sig.Bubble, (forget E).ops.hasRevision B_E →
        ∀ d_E d'_E : (forget E).sig.Deposit,
        (forget E).ops.revise B_E d_E d'_E → (forget E).ops.truth B_E d'_E) :=
  ⟨transport_self_correction,
   transport_safe_withdrawal,
   transport_reliable_export,
   transport_sound_deposits,
   transport_corrigible_universal⟩


/-! ## 8. Lattice-Stability: Sub-bundle Modularity -/

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

/-- ModularityPack: the full bidirectional lattice-stability result.

    Component 1 — Graceful Degradation (downward):
      Any sub-bundle with NoSelfCorrection satisfies RevisionGate.
    Component 2 — Sub-level RevisionSafety (downward then upward):
      Compatible extension of any sub-bundle with RevisionGate → RevisionGate preserved.
    Component 3 — Full-level RevisionSafety (upward):
      Compatible extension of the full bundle → RevisionGate preserved.

    Together: EpArch is a floor, not a cage. -/
theorem modularity_pack :
    -- (1) Graceful degradation
    (∀ (M : CoreModel), NoSelfCorrection M → RevisionGate M) ∧
    -- (2) Sub-level revision safety
    (∀ (S : SubBundle) (E : ExtModel),
        Compatible E S.model → RevisionGate S.model → RevisionGate (forget E)) ∧
    -- (3) Full-level revision safety
    (∀ (C : CoreModel) (R : RevisionSafeExtension C),
        RevisionGate C → RevisionGate (forget R.ext)) :=
  ⟨graceful_degradation, sub_revision_safety, safe_extension_preserves⟩

end EpArch.Meta.TheoremTransport
