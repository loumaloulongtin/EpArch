/-
EpArch.ResidualRiskMitigation — Residual Risk Mitigation Coverage (T27)

Classification theorem: every residual-risk mode induced by bounded autonomous
novelty handling is covered by a prescribed EpArch mechanism.

Key exports:
- `ResidualRiskMode`: nine structural failure modes induced by the operating regime
- `EpArchMechanism`: eleven prescribed architectural mechanisms
- `Mitigates`: inductive relation; each constructor is definitional evidence for a pairing
- `eparch_surface_covers_residual_risk_modes`: capstone coverage theorem (T27)
-/

import EpArch.Health
import EpArch.Minimality
import EpArch.Header
import EpArch.Bank
import EpArch.Commitments

namespace EpArch

/-! ## ResidualRiskMode — Structural Failure Mode Taxonomy

The nine distinct failure modes that remain once risk-free autonomous novelty
handling is unavailable.  Each constructor names a mode, not an implementation
defect.  The modes exist because the operating regime (bounded verification +
PRP + novel inputs) generates them structurally; T25–T26 explain why. -/

/-- The distinct structural failure modes that remain once risk-free autonomous
    novelty handling is unavailable.  Each constructor names a mode, not an
    implementation defect: the mode exists because the operating regime (bounded
    verification + PRP + novel inputs) generates it structurally.

    - `scopeLeak`:         a claim valid in one bubble is silently imported and
                           relied on outside the scope where it was verified.
    - `standardMismatch`:  no explicit acceptance threshold; the wrong standard
                           is applied at reliance time.
    - `unmodeledError`:    known failure modes or uncertainty are not recorded;
                           they propagate silently through bridge reliance.
    - `provenanceGap`:     source / chain dependency is invisible at reliance time;
                           bridge origin cannot be audited or challenged.
    - `staleness`:         a time-sensitive claim is relied on past its freshness
                           window; no mechanism enforces temporal validity.
    - `adversarialImport`: an untrusted actor submits or promotes a deposit;
                           no authorization gate is enforced.
    - `unrevokedDefect`:   a defective deposit is not revoked; the challenge and
                           correction path is absent or blocked.
    - `overbudgetReliance`: bridge reliance hides the verification gap and is
                           treated operationally as if it were scratch
                           verification; the gap is unlabelled rather than
                           structurally absent.
    - `unsafeAutonomy`:    autonomous action is taken without a sound non-action
                           branch; the escalation path is structurally absent. -/
inductive ResidualRiskMode where
  | scopeLeak
  | standardMismatch
  | unmodeledError
  | provenanceGap
  | staleness
  | adversarialImport
  | unrevokedDefect
  | overbudgetReliance
  | unsafeAutonomy
  deriving DecidableEq, Repr

/-! ## EpArchMechanism — Prescribed Architectural Surface

The eleven mechanisms that compose the EpArch mitigation surface.  Each is
present because it mitigates at least one `ResidualRiskMode` that the operating
regime forces.  The surface is prescribed by the architecture; T27 establishes
coverage, T28 establishes irredundancy. -/

/-- The EpArch mechanisms that compose the mitigation surface.
    Each constructor names a structural mechanism; each is present because it
    mitigates at least one `ResidualRiskMode` that the operating regime forces.
    The surface is prescribed by the architecture, not proved irredundant here:
    T27 establishes coverage, not minimality in the strict sense.
    The `Mitigates` inductive below contains one or more constructors
    for every mechanism. -/
inductive EpArchMechanism where
  | bubbles           -- scope isolation: claims are localised to bubbles
  | standardsHeader   -- S-field: explicit acceptance threshold
  | errorHeader       -- E-field: uncertainty / failure-mode record
  | provenanceHeader  -- V-field: source / chain dependency
  | tau               -- τ-field: temporal validity window
  | trustBridge       -- analogical import with explicit verification gap
  | authorization     -- ACL: submit / promote / update permissions
  | bankLifecycle     -- Candidate → Deposited → Quarantined → Revoked / Forgotten
  | redeemability     -- challenge + required correction path
  | boundedRecall     -- recall-admissibility filtering (Minimality §9)
  | escalation        -- principled non-action / referral branch (T25)
  deriving DecidableEq, Repr

/-! ## Mitigates — Coverage Relation

`Mitigates m r` holds when mechanism `m` converts residual-risk mode `r` from
an unstructured failure possibility into an auditable operational obligation.
Each constructor is definitional evidence; the doc-comment names the grounding
(upstream theorem or structural invariant). -/

/-- `Mitigates m r` holds when mechanism `m` converts residual-risk mode `r`
    from an unstructured failure possibility into an auditable operational
    obligation.  The inductive constructors are the evidence: each names the
    specific structural reason why the pairing holds. -/
inductive Mitigates : EpArchMechanism → ResidualRiskMode → Prop where
  /-- Bubbles localise validity: every deposit carries a `bubble` field
      (`Deposit.bubble`) that records the scope in which it was verified;
      bank-side predicates such as `deposited B d` enforce locality.
      (`Header` carries S/E/V/τ/acl/redeem; the bubble is on `Deposit`, not `Header`.)
      Scope-leak is converted into a structural locality obligation. -/
  | bubbles_scope_leak      : Mitigates .bubbles .scopeLeak
  /-- The S-header makes the acceptance standard explicit in the deposit record.
      `Deposit.Header.S : Standard` is a required field; the acceptance threshold
      is never implicit.
      Standard-mismatch is converted into a field-level audit obligation. -/
  | standards_mismatch      : Mitigates .standardsHeader .standardMismatch
  /-- The E-header records known error modes and uncertainty at deposit time.
      `Deposit.Header.E : ErrorModel` is a required field; known failure modes
      are declared at deposit time or the field is absent and visible.
      Unmodeled-error risk is converted into a declared-uncertainty obligation. -/
  | error_unmodeled         : Mitigates .errorHeader .unmodeledError
  /-- The V-header exposes the source and chain dependency of every deposit.
      `Deposit.Header.V : Provenance` is a required field; `PathExists.ttl_valid`
      and `status_live` make the path auditable.
      Provenance-gap risk is converted into a traceable-origin obligation. -/
  | provenance_gap          : Mitigates .provenanceHeader .provenanceGap
  /-- τ makes temporal validity part of the deposit record; `τ = 0` blocks
      path existence (`PathExists`).  Staleness risk is converted into a
      freshness-enforcement obligation. -/
  | tau_staleness           : Mitigates .tau .staleness
  /-- `Header.acl` records the authorization surface for every deposit;
      `Action` constructors carry agent attribution.  Authorization forcing
      is modeled at the agent/configuration layer (`AuthorizedWithdrawalGoal`,
      `TwoTierAccess`, and granular ACL results), while the abstract bank LTS
      deliberately does not enforce ACL as a Step precondition.
      Adversarial-import risk is converted into a declared authorization obligation. -/
  | auth_adversarial        : Mitigates .authorization .adversarialImport
  /-- The bank lifecycle provides Challenge/Repair/Revoke transitions:
      `challenge_produces_quarantined`, `Repair_B_produces_candidate`,
      and `revoke_produces_revoked` in `Bank.lean` witness the abstract
      lifecycle; `Step.challenge`, `Step.repair`, and `Step.revoke` in
      `StepSemantics.lean` operationalize the same correction surface.
      Unrevoked-defect risk is converted into a revocation/repair obligation. -/
  | lifecycle_defect        : Mitigates .bankLifecycle .unrevokedDefect
  /-- A trust bridge carries an explicit verification gap (`residualRiskVia`);
      overbudget reliance is labelled, not hidden.
      `risk_not_eliminable_by_budgeted_bridge` (Minimality §11) shows why the
      gap is irreducible; the bridge mechanism makes it explicit rather than hidden.
      Overbudget-reliance risk is converted into an explicit gap-labelling obligation. -/
  | bridge_overbudget       : Mitigates .trustBridge .overbudgetReliance
  /-- The escalation branch (`canEscalate`) is the sound non-action path.
      `no_escalation_forces_bridge` (Health.lean, T25) shows that without it
      the system is forced to bridge-or-nothing; with it, unsafe autonomous
      action is not the only remaining option.
      Unsafe-autonomy risk is converted into a principled-referral obligation. -/
  | escalation_unsafe       : Mitigates .escalation .unsafeAutonomy
  /-- Redeemability makes the challenge-and-correction path explicit and
      required: `redeemable d` (`Commitments.lean`) requires a `VerificationPath`
      aligned to `d.h.redeem`; `challenge_produces_quarantined` (`Bank.lean`)
      shows the first step of the correction pipeline is closed.
      (`PathExists.status_live` separately carries the non-revoked precondition
      for adversarial path obligations — a distinct proof surface.)
      An unrevoked defect without a redeemability structure has no correction
      obligation; with it, the obligation is explicit and auditable. -/
  | redeemability_defect    : Mitigates .redeemability .unrevokedDefect
  /-- Bounded-recall discipline (Minimality §9: `recall_only_withdrawal_incomplete`)
      shows that provenance chains exceeding the recall budget make recall-only
      verification structurally incomplete.  The `boundedRecall` mechanism
      prevents silent over-reliance: old deposits that exhaust the recall budget
      are filtered, converting silent overbudget reliance into an explicit
      scope failure. -/
  | bounded_recall_overbudget : Mitigates .boundedRecall .overbudgetReliance

/-! ## Coverage Theorem (T27)

`eparch_surface_covers_residual_risk_modes` is the capstone classification
theorem: every declared residual-risk mode is answered by some EpArch
mechanism.  The proof is zero-cost — each `cases r` branch supplies the
matching `Mitigates` constructor. -/

/-- EPARCH SURFACE COVERS FORCED RESIDUAL RISK MODES

    Every residual-risk mode induced by bounded autonomous novelty handling
    is covered by an EpArch mechanism that makes that mode an auditable
    operational obligation rather than an unstructured failure possibility.

    **Theorem shape:** `∀ r : ResidualRiskMode, ∃ m : EpArchMechanism, Mitigates m r`
    **Proof strategy:** `cases r`; supply the matching `Mitigates` constructor.

    This theorem is a classification theorem, not an impossibility theorem.
    The structural depth lives in T25–T26: those results explain why the
    nine risk modes are not arbitrary.  This theorem shows that EpArch's
    surface is *complete* with respect to those modes — no mode is left
    unaddressed.

    Does not say: the mechanisms eliminate the underlying risk.  `Mitigates m r`
    states that mechanism `m` converts risk mode `r` into an auditable obligation;
    whether that obligation is correctly discharged is a system-level property,
    not an architectural guarantee.

    Does not say: each mechanism addresses exactly one mode.  The existence
    theorem requires only coverage; multiple mechanisms may address the same
    mode, and a single mechanism may address multiple modes.

    Exhaustiveness: this theorem is exhaustive over the declared
    `ResidualRiskMode` inductive.  Adding a new constructor to
    `ResidualRiskMode` breaks the proof until a new `Mitigates` constructor
    and a new case branch are supplied — the coverage guarantee is
    machine-checked, not informal. -/
theorem eparch_surface_covers_residual_risk_modes :
    ∀ r : ResidualRiskMode, ∃ m : EpArchMechanism, Mitigates m r := by
  intro r; cases r with
  | scopeLeak         => exact ⟨.bubbles,         .bubbles_scope_leak⟩
  | standardMismatch  => exact ⟨.standardsHeader, .standards_mismatch⟩
  | unmodeledError    => exact ⟨.errorHeader,      .error_unmodeled⟩
  | provenanceGap     => exact ⟨.provenanceHeader, .provenance_gap⟩
  | staleness         => exact ⟨.tau,              .tau_staleness⟩
  | adversarialImport => exact ⟨.authorization,   .auth_adversarial⟩
  | unrevokedDefect   => exact ⟨.bankLifecycle,    .lifecycle_defect⟩
  | overbudgetReliance => exact ⟨.trustBridge,    .bridge_overbudget⟩
  | unsafeAutonomy    => exact ⟨.escalation,       .escalation_unsafe⟩

end EpArch
