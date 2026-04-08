/-
EpArch/Meta/Tier4Transport.lean — Tier 4 Transport Closure

Certifies that all theorem clusters in the main library (Theorems.lean,
Commitments.lean) are machine-checked and transport-safe.

## The Clusters

### Cluster A — Standalone commitments theorem family

All 8 architectural commitments are proved standalone theorems in Commitments.lean.
`commitments_pack` bundles the unconditional ones (C3/C7b/C8); C1, C2, C4b, C5, C6b
are proved as separately named theorems.  Cluster A is an unconditional theorem
family — no transport machinery needed, no hypothesis context to extend.

Key theorem family: `commitments_pack` (Commitments.lean).

### Cluster B — Standalone structural theorems

`SEVFactorization`, `TemporalValidity`, `monolithic_not_injective`,
`header_stripping_harder` carry no model hypothesis — universally valid.

Key theorem: `structural_theorems_unconditional`.

### Cluster C — Concrete bank: CoreModel bridge + full health-goal transport

Two sub-results:

**§3b — LTS-Universal Operational Theorems**
The withdrawal/repair/submit theorems from `Theorems.lean` are Cluster-B-style:
they hold for every `SystemState`/`Step` instance by virtue of constructor
preconditions. No model parameter varies, so no transport is needed.

Key theorem: `lts_theorems_step_universal`.

**§3c — All Five Health Goals Transport**
All five ∀-health goals (`SafeWithdrawalGoal`, `ReliableExportGoal`,
`SoundDepositsGoal`, `SelfCorrectionGoal`, universal `CorrigibleLedgerGoal`)
are preserved by any compatible extension of `ConcreteBankModel`.

Key theorem: `concrete_bank_all_goals_transport`.

## Coverage Table

| Cluster | Mechanism | Theorem |
|---|---|---|
| Standalone commitments (A) | All 8 commitments proved | `commitments_pack` |
| Standalone structural (B) | Unconditional (no transport needed) | `structural_theorems_unconditional` |
| LTS-universal operational (B+) | Step constructor completeness | `lts_theorems_step_universal` |
| All five health goals (C) | `transport_*` applied to ConcreteBankModel | `concrete_bank_all_goals_transport` |
| Full Tier 4 pack | Clusters B + C combined | `tier4_full_pack` |

-/

import EpArch.Commitments
import EpArch.Theorems
import EpArch.Meta.TheoremTransport

namespace EpArch.Meta.Tier4Transport

open RevisionSafety
open EpArch.Meta.TheoremTransport

variable {PropLike Standard ErrorModel Provenance : Type}


/-! ## §1  Cluster A: Standalone Commitments Family -/

/-! All 8 architectural commitments are proved standalone theorems in `Commitments.lean`.
    `commitments_pack` packages the four universally-closable commitment theorems
    (C3/C4b/C7b/C8); C4b (`redeemability_requires_more_than_consensus`) is the
    commitment-specific result that distinguishes A from `structural_theorems_unconditional` (B).
    No transport structure is needed: the theorems are unconditional. -/


/-! ## §2  Cluster B: Standalone Structural Theorems -/

/-- Structural theorems are transport-vacuous: they hold in every sub-bundle.

    (1) SEV factorization
    (2) Temporal validity
    (3) Monolithic non-injectivity
    (4) Header-stripped diagnosability is lower -/
theorem structural_theorems_unconditional :
    (∀ (d : Deposit PropLike Standard ErrorModel Provenance),
        ∃ (s : Standard) (e : ErrorModel) (v : Provenance),
          d.h.S = s ∧ d.h.E = e ∧ d.h.V = v) ∧
    (∀ (d1 d2 : Deposit PropLike Standard ErrorModel Provenance),
        refreshed d1 → unrefreshed d2 → ¬performs_equivalently d1 d2) ∧
    (¬∀ f1 f2 : FailureField, FailMonolithic f1 = FailMonolithic f2 → f1 = f2) ∧
    systematically_harder header_preserved_diagnosability header_stripped_diagnosability :=
  ⟨SEVFactorization, TemporalValidity, monolithic_not_injective, header_stripping_harder⟩


/-! ## §3  Cluster C: Concrete Bank = CoreModel Bridge -/

/-- Bundle of concrete bank operations, eliminating the 8-argument repetition
    across theorem signatures.  Construct once and reuse everywhere.

    For the vacuous base case (selfCorrects always False), use record update:
    `{ ops with selfCorr_pred := fun _ => False }`. -/
structure ConcreteBankOps (PropLike Standard ErrorModel Provenance : Type) where
  truth_pred    : Bubble → Deposit PropLike Standard ErrorModel Provenance → Prop
  obs_pred      : Deposit PropLike Standard ErrorModel Provenance → Prop
  verify_pred   : Bubble → Deposit PropLike Standard ErrorModel Provenance → Time → Prop
  etime         : Bubble → Time
  submit_pred   : Agent → Bubble → Deposit PropLike Standard ErrorModel Provenance → Prop
  revise_pred   : Bubble → Deposit PropLike Standard ErrorModel Provenance →
                  Deposit PropLike Standard ErrorModel Provenance → Prop
  hasRev_pred   : Bubble → Prop
  selfCorr_pred : Bubble → Prop

/-- `ConcreteBankModel`: a `CoreModel` whose signature uses the concrete EpArch
    bank types and whose operations are supplied via `ConcreteBankOps`.

    The caller provides world-layer and bank-layer predicates
    (e.g. from WorldCtx.Truth or StepSemantics.Step).
    `deposit_header` is fixed as the structural projection `d.h`. -/
noncomputable def ConcreteBankModel
    (ops : ConcreteBankOps PropLike Standard ErrorModel Provenance)
    : CoreModel where
  sig := {
    Agent   := EpArch.Agent
    Claim   := PropLike
    Bubble  := EpArch.Bubble
    Time    := EpArch.Time
    Deposit := EpArch.Deposit PropLike Standard ErrorModel Provenance
    Header  := EpArch.Header Standard ErrorModel Provenance
  }
  ops := {
    deposit_header := fun d => d.h
    truth          := ops.truth_pred
    obs            := ops.obs_pred
    verifyWithin   := ops.verify_pred
    effectiveTime  := ops.etime
    submit         := ops.submit_pred
    revise         := ops.revise_pred
    hasRevision    := ops.hasRev_pred
    selfCorrects   := ops.selfCorr_pred
  }
  hasBubble := ⟨default⟩

/-- `ConcreteBankModel` with `selfCorrects := fun _ => False` is PaperFacing.
    The competition gate holds vacuously since the premise is always False. -/
theorem concrete_bank_vacuous_pf
    (ops : ConcreteBankOps PropLike Standard ErrorModel Provenance) :
    PaperFacing (ConcreteBankModel { ops with selfCorr_pred := fun _ => False }) :=
  fun _B h_sc => h_sc.elim

/-- Compatible extensions of `ConcreteBankModel` preserve `PaperFacing`.
    Direct application of `transport_self_correction`. -/
theorem concrete_bank_transport
    (ops : ConcreteBankOps PropLike Standard ErrorModel Provenance)
    (E : ExtModel)
    (h_compat : Compatible E (ConcreteBankModel ops))
    (h_pf : PaperFacing (ConcreteBankModel ops)) :
    PaperFacing (forget E) :=
  transport_self_correction E _ h_compat h_pf

/-- Vacuous concrete bank extension: specialises `concrete_bank_transport` to
    the base case where `selfCorrects` is always False. -/
theorem concrete_bank_vacuous_transport
    (ops : ConcreteBankOps PropLike Standard ErrorModel Provenance)
    (E : ExtModel)
    (h_compat : Compatible E (ConcreteBankModel { ops with selfCorr_pred := fun _ => False })) :
    PaperFacing (forget E) :=
  transport_self_correction E _
    h_compat
    (concrete_bank_vacuous_pf ops)


/-! ## §3b  LTS-Universal Theorems (Operational Layer)

The concrete operational theorems from `Theorems.lean` mirror Cluster B:
they are universally valid about the `Step` LTS and hold for **every**
`SystemState` instance with no model parameter to transport.

Key results certified here: withdrawal gates, repair revalidation,
repair quarantine requirement, submit Candidate lifecycle. -/

/-- LTS operational theorems are unconditionally valid about the concrete `Step` LTS.

    Like `structural_theorems_unconditional`, no model parameter varies here:
    these hold by virtue of what the `Step` constructors require and produce.

    (1) Withdrawal gates: `Step.Withdraw` fires only with ACL + current τ + Deposited.
    (2) Repair revalidation: `Step.Repair` produces Candidate status in the ledger.
    (3) Repair quarantine: `Step.Repair` requires Quarantined input status.
    (4) Submit Candidate: `Step.Submit` ensures at least one Candidate deposit. -/
theorem lts_theorems_step_universal {Reason Evidence : Type} :
    (∀ (s s' : StepSemantics.SystemState PropLike Standard ErrorModel Provenance)
       (B : Bubble) (a : Agent) (d_idx : Nat),
       StepSemantics.Step (Reason := Reason) (Evidence := Evidence)
         s (StepSemantics.Action.Withdraw a B d_idx) s' →
       ACL_OK_At s a B d_idx ∧ Current_At s d_idx ∧ ConsultedBank_At s d_idx) ∧
    (∀ (s s' : StepSemantics.SystemState PropLike Standard ErrorModel Provenance)
       (d_idx : Nat) (f : Field),
       StepSemantics.Step (Reason := Reason) (Evidence := Evidence)
         s (StepSemantics.Action.Repair d_idx f) s' →
       s'.ledger = StepSemantics.updateDepositStatus s.ledger d_idx .Candidate) ∧
    (∀ (s s' : StepSemantics.SystemState PropLike Standard ErrorModel Provenance)
       (d_idx : Nat) (f : Field),
       StepSemantics.Step (Reason := Reason) (Evidence := Evidence)
         s (StepSemantics.Action.Repair d_idx f) s' →
       StepSemantics.isQuarantined s d_idx) ∧
    (∀ (s s' : StepSemantics.SystemState PropLike Standard ErrorModel Provenance)
       (d : Deposit PropLike Standard ErrorModel Provenance),
       StepSemantics.Step (Reason := Reason) (Evidence := Evidence)
         s (StepSemantics.Action.Submit d) s' →
       ∃ d', d' ∈ s'.ledger ∧ d'.status = DepositStatus.Candidate) :=
  ⟨fun s s' B a d_idx h => withdrawal_gates s s' B a d_idx h,
   fun s s' d_idx f h => repair_enforces_revalidation s s' d_idx f h,
   fun s s' d_idx f h => repair_requires_prior_challenge s s' d_idx f h,
   fun s s' d h      => submit_enforces_revalidation s s' d h⟩


/-! ## §3c  All Five Health Goals Transport Through ConcreteBankModel

This section closes the actual Cluster C gap: not just the competition gate
(PaperFacing / SelfCorrectionGoal) but **all five** ∀-health goals survive
any compatible extension of a concrete-bank-shaped CoreModel.

Proof: direct application of the five individual transport theorems from
`TheoremTransport.lean` to a `ConcreteBankModel` +  `Compatible` witness.

Note: the ∃-component of `CorrigibleLedgerGoal` requires `SurjectiveCompatible`
(see `transport_corrigible_ledger`). This theorem covers the universal part. -/

/-- All five ∀-health-goals are preserved by any compatible extension of
    `ConcreteBankModel`.

    Given that the base concrete-bank model satisfies each health goal,
    any compatible extension (via `forget`) satisfies all five goals:
    (1) SafeWithdrawalGoal  (2) ReliableExportGoal  (3) SoundDepositsGoal
    (4) SelfCorrectionGoal  (5) universal CorrigibleLedgerGoal. -/
theorem concrete_bank_all_goals_transport
    (ops : ConcreteBankOps PropLike Standard ErrorModel Provenance)
    (E : ExtModel)
    (h_compat : Compatible E (ConcreteBankModel ops))
    (h_sw : SafeWithdrawalGoal (ConcreteBankModel ops))
    (h_re : ReliableExportGoal (ConcreteBankModel ops))
    (h_sd : SoundDepositsGoal (ConcreteBankModel ops))
    (h_sc : SelfCorrectionGoal (ConcreteBankModel ops))
    (h_cl : CorrigibleLedgerGoal (ConcreteBankModel ops)) :
    SafeWithdrawalGoal (forget E) ∧
    ReliableExportGoal (forget E) ∧
    SoundDepositsGoal (forget E) ∧
    SelfCorrectionGoal (forget E) ∧
    (∀ B_E : (forget E).sig.Bubble, (forget E).ops.hasRevision B_E →
     ∀ d_E d'_E : (forget E).sig.Deposit,
     (forget E).ops.revise B_E d_E d'_E → (forget E).ops.truth B_E d'_E) :=
  ⟨transport_safe_withdrawal E _ h_compat h_sw,
   transport_reliable_export E _ h_compat h_re,
   transport_sound_deposits E _ h_compat h_sd,
   transport_self_correction E _ h_compat h_sc,
   transport_corrigible_universal E _ h_compat h_cl⟩


/-! ## §3d  Full CorrigibleLedgerGoal Transport (SurjectiveCompatible)

`concrete_bank_all_goals_transport` (§3c) returns only the ∀-part of
`CorrigibleLedgerGoal` because plain `Compatible` cannot pull back the existence
witness `∃ B, hasRevision B` — the projection πBubble goes E → C, not C → E.

`SurjectiveCompatible` adds `bubbleSurj` (every C-bubble has a preimage in E),
which is exactly the missing pullback. With it, `transport_corrigible_ledger`
constructs the full `CorrigibleLedgerGoal (forget E)`. -/

/-- All five health goals transport through surjective-compatible extensions of
    `ConcreteBankModel`, with **full** `CorrigibleLedgerGoal` (∃ + ∀ components).

    Strengthens `concrete_bank_all_goals_transport`: the only change is the
    compatibility hypothesis (SurjectiveCompatible instead of Compatible) and the
    return type replaces the bare ∀-clause with `CorrigibleLedgerGoal (forget E)`. -/
theorem concrete_bank_all_goals_transport_surj
    (ops : ConcreteBankOps PropLike Standard ErrorModel Provenance)
    (E : ExtModel)
    (h_compat : SurjectiveCompatible E (ConcreteBankModel ops))
    (h_sw : SafeWithdrawalGoal (ConcreteBankModel ops))
    (h_re : ReliableExportGoal (ConcreteBankModel ops))
    (h_sd : SoundDepositsGoal (ConcreteBankModel ops))
    (h_sc : SelfCorrectionGoal (ConcreteBankModel ops))
    (h_cl : CorrigibleLedgerGoal (ConcreteBankModel ops)) :
    SafeWithdrawalGoal (forget E) ∧
    ReliableExportGoal (forget E) ∧
    SoundDepositsGoal (forget E) ∧
    SelfCorrectionGoal (forget E) ∧
    CorrigibleLedgerGoal (forget E) :=
  ⟨transport_safe_withdrawal E _ h_compat.toCompatible h_sw,
   transport_reliable_export E _ h_compat.toCompatible h_re,
   transport_sound_deposits E _ h_compat.toCompatible h_sd,
   transport_self_correction E _ h_compat.toCompatible h_sc,
   transport_corrigible_ledger E _ h_compat h_cl⟩


/-! ## §4  Full Tier 4 Certification -/

/-- `tier4_transport_pack` — legacy pack (PaperFacing only, vacuous base).

    Kept for backward compatibility. For the full Cluster C certification
    (all five health goals), use `tier4_full_pack`. -/
theorem tier4_transport_pack
    (ops : ConcreteBankOps PropLike Standard ErrorModel Provenance)
    (E_bank   : ExtModel)
    (h_compat : Compatible E_bank
        (ConcreteBankModel { ops with selfCorr_pred := fun _ => False })) :
    (∀ (d : Deposit PropLike Standard ErrorModel Provenance),
        ∃ (s : Standard) (e : ErrorModel) (v : Provenance),
          d.h.S = s ∧ d.h.E = e ∧ d.h.V = v) ∧
    PaperFacing (forget E_bank) :=
  ⟨SEVFactorization,
   concrete_bank_vacuous_transport ops E_bank h_compat⟩

/-- `tier4_full_pack` — complete Tier 4 transport certification.

    Packages three theorem clusters:
    (B1) Structural (Cluster B): SEVFactorization is unconditionally valid.
    (B2) LTS-universal (B extended): withdrawal gates are universally valid for every Step.
         (The full four-fact LTS pack is in `lts_theorems_step_universal`.)
    (C1–C5) Four full ∀-health goals and universal corrigibility (Cluster C):
         SafeWithdrawalGoal, ReliableExportGoal, SoundDepositsGoal, SelfCorrectionGoal
         transport through any Compatible extension; ∀-part of CorrigibleLedgerGoal
         also transports under plain Compatible.
         (The ∃-part of CorrigibleLedgerGoal requires SurjectiveCompatible.)

    Note: Cluster A (standalone commitments) is not included here — this pack
    covers Clusters B + C only.  `commitments_pack` in Commitments.lean certifies
    C3/C4b/C7b/C8 unconditionally; C1/C2/C5/C6b are proved as named theorems. -/
theorem tier4_full_pack
    {Reason Evidence : Type}
    (ops    : ConcreteBankOps PropLike Standard ErrorModel Provenance)
    (E_bank : ExtModel)
    (h_compat : Compatible E_bank (ConcreteBankModel ops))
    (h_sw : SafeWithdrawalGoal (ConcreteBankModel ops))
    (h_re : ReliableExportGoal (ConcreteBankModel ops))
    (h_sd : SoundDepositsGoal (ConcreteBankModel ops))
    (h_sc : SelfCorrectionGoal (ConcreteBankModel ops))
    (h_cl : CorrigibleLedgerGoal (ConcreteBankModel ops)) :
    -- (B1) Structural: SEV factorization holds unconditionally
    (∀ (d : Deposit PropLike Standard ErrorModel Provenance),
        ∃ (s : Standard) (e : ErrorModel) (v : Provenance),
          d.h.S = s ∧ d.h.E = e ∧ d.h.V = v) ∧
    -- (B2) LTS-universal: withdrawal requires all three gates for every Step
    (∀ (s s' : StepSemantics.SystemState PropLike Standard ErrorModel Provenance)
       (B : Bubble) (a : Agent) (d_idx : Nat),
       StepSemantics.Step (Reason := Reason) (Evidence := Evidence)
         s (StepSemantics.Action.Withdraw a B d_idx) s' →
       ACL_OK_At s a B d_idx ∧ Current_At s d_idx ∧ ConsultedBank_At s d_idx) ∧
    -- (C1) SafeWithdrawalGoal transports through compatible bank extension
    SafeWithdrawalGoal (forget E_bank) ∧
    -- (C2) ReliableExportGoal transports
    ReliableExportGoal (forget E_bank) ∧
    -- (C3) SoundDepositsGoal transports
    SoundDepositsGoal (forget E_bank) ∧
    -- (C4) SelfCorrectionGoal (= PaperFacing) transports
    SelfCorrectionGoal (forget E_bank) ∧
    -- (C5) Universal CorrigibleLedgerGoal: hasRevision → revision preserves truth (∀-part)
    --     The ∃-part requires SurjectiveCompatible; this is what Compatible alone guarantees.
    (∀ B_E : (forget E_bank).sig.Bubble, (forget E_bank).ops.hasRevision B_E →
     ∀ d_E d'_E : (forget E_bank).sig.Deposit,
     (forget E_bank).ops.revise B_E d_E d'_E → (forget E_bank).ops.truth B_E d'_E) :=
  let lts   := @lts_theorems_step_universal PropLike Standard ErrorModel Provenance Reason Evidence
  let goals := concrete_bank_all_goals_transport ops E_bank h_compat h_sw h_re h_sd h_sc h_cl
  ⟨SEVFactorization,
   lts.1,
   goals.1,
   goals.2.1,
   goals.2.2.1,
   goals.2.2.2.1,
   goals.2.2.2.2⟩

/-- `tier4_full_pack_surj` — headline theorem with full CorrigibleLedgerGoal.

    Identical to `tier4_full_pack` except:
    - Takes `SurjectiveCompatible` instead of `Compatible`.
    - Conjunct (C5) is `CorrigibleLedgerGoal (forget E_bank)` (∃ + ∀),
      not just the universal clause.

    This is the maximal Tier 4 certification: all five health goals transport
    completely, with no residual ∃-witness caveat. -/
theorem tier4_full_pack_surj
    {Reason Evidence : Type}
    (ops    : ConcreteBankOps PropLike Standard ErrorModel Provenance)
    (E_bank : ExtModel)
    (h_compat : SurjectiveCompatible E_bank (ConcreteBankModel ops))
    (h_sw : SafeWithdrawalGoal (ConcreteBankModel ops))
    (h_re : ReliableExportGoal (ConcreteBankModel ops))
    (h_sd : SoundDepositsGoal (ConcreteBankModel ops))
    (h_sc : SelfCorrectionGoal (ConcreteBankModel ops))
    (h_cl : CorrigibleLedgerGoal (ConcreteBankModel ops)) :
    -- (B1) Structural: SEV factorization holds unconditionally
    (∀ (d : Deposit PropLike Standard ErrorModel Provenance),
        ∃ (s : Standard) (e : ErrorModel) (v : Provenance),
          d.h.S = s ∧ d.h.E = e ∧ d.h.V = v) ∧
    -- (B2) LTS-universal: withdrawal requires all three gates for every Step
    (∀ (s s' : StepSemantics.SystemState PropLike Standard ErrorModel Provenance)
       (B : Bubble) (a : Agent) (d_idx : Nat),
       StepSemantics.Step (Reason := Reason) (Evidence := Evidence)
         s (StepSemantics.Action.Withdraw a B d_idx) s' →
       ACL_OK_At s a B d_idx ∧ Current_At s d_idx ∧ ConsultedBank_At s d_idx) ∧
    -- (C1) SafeWithdrawalGoal transports
    SafeWithdrawalGoal (forget E_bank) ∧
    -- (C2) ReliableExportGoal transports
    ReliableExportGoal (forget E_bank) ∧
    -- (C3) SoundDepositsGoal transports
    SoundDepositsGoal (forget E_bank) ∧
    -- (C4) SelfCorrectionGoal (= PaperFacing) transports
    SelfCorrectionGoal (forget E_bank) ∧
    -- (C5) Full CorrigibleLedgerGoal transports (∃-witness pulled back via bubbleSurj)
    CorrigibleLedgerGoal (forget E_bank) :=
  let lts   := @lts_theorems_step_universal PropLike Standard ErrorModel Provenance Reason Evidence
  let goals := concrete_bank_all_goals_transport_surj ops E_bank h_compat h_sw h_re h_sd h_sc h_cl
  ⟨SEVFactorization,
   lts.1,
   goals.1,
   goals.2.1,
   goals.2.2.1,
   goals.2.2.2.1,
   goals.2.2.2.2⟩

end EpArch.Meta.Tier4Transport
