/-
EpArch.ResidualRiskMitigation — Residual Risk Mitigation Coverage (T27 / T27b)

Classification theorem (T27a): every residual-risk mode induced by bounded autonomous
novelty handling is covered by a prescribed EpArch mechanism.

Grounded coverage layer (T27b): companion proof-grounded relation showing that every
residual-risk mode has a mitigation pairing backed by upstream theorem evidence or
concrete structural field/projection evidence.

Key exports:
- `ResidualRiskMode`: nine structural failure modes induced by the operating regime
- `EpArchMechanism`: eleven prescribed architectural mechanisms
- `Mitigates`: declared coverage relation; each constructor is definitional evidence for a pairing
- `eparch_surface_covers_residual_risk_modes`: capstone coverage theorem (T27a)
- `GroundedMitigates`: proof-backed companion; each constructor carries upstream theorem or
  structural projection evidence
- `grounded_mitigation_implies_mitigation`: T27b implies T27a
- `eparch_surface_groundedly_covers_residual_risk_modes`: grounded coverage theorem (T27b)
-/

import EpArch.Health
import EpArch.Minimality
import EpArch.Header
import EpArch.Bank
import EpArch.Commitments
import EpArch.Adversarial.Obligations

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

/-! ========================================================================
    GROUNDED COVERAGE LAYER (T27b) — Proof-Backed Mitigation Evidence
    ========================================================================

    T27a establishes declared coverage: every `ResidualRiskMode` has some
    `Mitigates` pairing.  `Mitigates` constructors are definitional evidence —
    they name the mechanism and the mode, backed by doc-comment reasoning.

    T27b adds a companion layer: `GroundedMitigates` requires that each
    constructor carry *actual proof evidence* — either an upstream theorem
    (applied to its real inputs) or a structural projection from an existing
    field.  This makes the coverage machine-verifiable in depth, not just
    in classification.

    Scope:
    - Does NOT prove strict minimality / irredundancy of the surface.  That is T28.
    - Does NOT use `True`, `trivial`, or fake evidence arguments.
    - Does NOT mutate `Mitigates` or delete T27a.
    - Each upstream-theorem case carries the theorem as a function value.
    - Each structural case carries a field-projection proposition proved by `rfl`. -/

/-! ## GroundedMitigates — Proof-Backed Coverage Relation -/

/-- `GroundedMitigates m r` is the proof-backed companion to `Mitigates m r`.

    Each constructor carries an actual evidence argument: either an upstream
    theorem (as a function applied to its proper hypotheses) or a structural
    projection from a required field.  The evidence is not a bare constructor
    tag but a proof obligation whose content can be inspected.

    - Upstream-theorem constructors carry a universally-quantified function
      whose body is an application of the named theorem.
    - Structural-projection constructors carry a proposition proved by `rfl`
      (a field-projection fact), confirming that the required field exists
      and is accessible on every record of the relevant type.

    `grounded_mitigation_implies_mitigation` shows this relation implies
    `Mitigates`; `eparch_surface_groundedly_covers_residual_risk_modes`
    proves grounded coverage exhaustively. -/
inductive GroundedMitigates : EpArchMechanism → ResidualRiskMode → Prop where

  /-- Scope isolation grounded by structural projection.
      Every `Deposit` carries a `bubble : Bubble` field.  The scope of a
      deposit is not implicit or inferred — it is a required record component.
      Grounding: `fun _ _ _ _ d => ⟨d.bubble, rfl⟩` — field projection from
      the `Deposit` structure definition in `EpArch.Header`. -/
  | bubbles_scope_leak :
      (∀ (PL S E P : Type) (d : Deposit PL S E P), ∃ b : Bubble, d.bubble = b) →
      GroundedMitigates .bubbles .scopeLeak

  /-- Standard enforcement grounded by structural projection.
      Every `Header` carries an `S : Standard` field.  The acceptance threshold
      is a required record component, never implicit.
      Grounding: `fun _ _ _ h => ⟨h.S, rfl⟩` — `Header.S` field projection. -/
  | standards_mismatch :
      (∀ (S E P : Type) (h : Header S E P), ∃ s : S, h.S = s) →
      GroundedMitigates .standardsHeader .standardMismatch

  /-- Error disclosure grounded by structural projection.
      Every `Header` carries an `E : ErrorModel` field.  Known failure modes
      are a required record component, not optional metadata.
      Grounding: `fun _ _ _ h => ⟨h.E, rfl⟩` — `Header.E` field projection. -/
  | error_unmodeled :
      (∀ (S E P : Type) (h : Header S E P), ∃ e : E, h.E = e) →
      GroundedMitigates .errorHeader .unmodeledError

  /-- Provenance traceability grounded by structural projection.
      Every `Header` carries a `V : Provenance` field.  Source and chain
      dependency are required record components.
      Grounding: `fun _ _ _ h => ⟨h.V, rfl⟩` — `Header.V` field projection. -/
  | provenance_gap :
      (∀ (S E P : Type) (h : Header S E P), ∃ v : P, h.V = v) →
      GroundedMitigates .provenanceHeader .provenanceGap

  /-- Temporal window enforcement grounded by `PathExists.ttl_valid`.
      `AdversarialObligations.PathExists d` requires `d.h.τ > 0` (`ttl_valid` field).
      A deposit with `τ = 0` structurally cannot carry a valid path witness.
      Grounding: `PathExists.ttl_valid : d.h.τ > 0` used directly via `omega`
      to derive `False` from `d.h.τ = 0 ∧ PathExists d`. -/
  | tau_staleness :
      (∀ (PL S E P : Type) (d : Deposit PL S E P),
          d.h.τ = 0 → ¬AdversarialObligations.PathExists d) →
      GroundedMitigates .tau .staleness

  /-- Authorization forcing grounded by `flat_authorization_impossible`.
      `flat_authorization_impossible (M : TwoTierAccess)` proves that no flat
      authorization predicate can represent both the submission tier and the
      commit tier — granular ACL is structurally forced.
      Grounding: `flat_authorization_impossible` from `EpArch.Minimality` §7. -/
  | auth_adversarial :
      (∀ (M : TwoTierAccess),
          ¬∃ (f : M.Agent → M.Claim → Prop),
            (∀ a c, f a c ↔ M.can_propose a c) ∧
            (∀ a c, f a c ↔ M.can_commit a c)) →
      GroundedMitigates .authorization .adversarialImport

  /-- Lifecycle correction grounded by `challenge_produces_quarantined`.
      A deposited record subjected to `Challenge_B` moves to `Quarantined`
      status — the first step of the correction pipeline is structurally
      closed.
      Grounding: `challenge_produces_quarantined` from `EpArch.Bank`. -/
  | lifecycle_defect :
      (∀ (PL S E P : Type) (B : Bubble) (d : Deposit PL S E P) (f : Field),
          d.status = .Deposited → (Challenge_B B d f).status = .Quarantined) →
      GroundedMitigates .bankLifecycle .unrevokedDefect

  /-- Overbudget-reliance grounded by `risk_not_eliminable_by_budgeted_bridge`.
      Any similar bridge that fits within the verification budget carries
      residual risk — the gap cannot be closed by cost-constrained bridging.
      Grounding: `risk_not_eliminable_by_budgeted_bridge` from `EpArch.Minimality` §11. -/
  | bridge_overbudget :
      (∀ (R : ResidualRiskBridge) (b : R.Bridge),
          R.sim b R.novel_claim →
          R.bridge_cost b R.novel_claim ≤ R.budget →
          ¬R.risk_free b R.novel_claim) →
      GroundedMitigates .trustBridge .overbudgetReliance

  /-- Escalation path grounded by `no_escalation_forces_bridge`.
      When an autonomy model satisfies `AutonomyUnderPRPGoal` and
      escalation is unavailable, a bridge is the only sound response.
      The escalation mechanism supplies the principled non-action branch
      that makes unsafe autonomous action structurally avoidable.
      Grounding: `no_escalation_forces_bridge` from `EpArch.Health` (T25). -/
  | escalation_unsafe :
      (∀ (M : AutonomyModel) (_ : AutonomyUnderPRPGoal M)
          (B : M.sig.Bubble) (d : M.sig.Deposit)
          (_ : M.ops.mustHandle B d)
          (_ : ¬M.ops.verifyWithin B d (M.ops.effectiveTime B))
          (_ : ¬M.ops.canEscalate B d),
          ∃ b : M.sig.Deposit,
            M.ops.bridgeAvailable B b ∧
            M.ops.analogSim b d ∧
            M.ops.verifyVia B b d (M.ops.effectiveTime B)) →
      GroundedMitigates .escalation .unsafeAutonomy

  /-- Redeemability obligation grounded by `redeemable_implies_surface_aligned`.
      A redeemable deposit has a `VerificationPath` aligned to `d.h.redeem`.
      The challenge-and-correction path is not merely declared — it is
      structurally required by the `redeemable` predicate.
      Grounding: `redeemable_implies_surface_aligned` from `EpArch.Commitments`. -/
  | redeemability_defect :
      (∀ (PL S E P : Type) (d : Deposit PL S E P),
          redeemable d →
          ∃ vp : VerificationPath (PropLike := PL) (Standard := S)
              (ErrorModel := E) (Provenance := P),
            vp.deposit = d ∧ vp.surface = d.h.redeem) →
      GroundedMitigates .redeemability .unrevokedDefect

  /-- Bounded-recall grounded by `recall_only_withdrawal_incomplete`.
      A fixed recall budget cannot re-verify all provenance chains:
      `¬∀ v : M.Provenance, M.recall_cost v ≤ M.budget`.
      This proves that silent recall-only withdrawal is incomplete,
      which is precisely the residual that `boundedRecall` makes explicit.
      Grounding: `recall_only_withdrawal_incomplete` from `EpArch.Minimality` §9. -/
  | bounded_recall_overbudget :
      (∀ (M : RecallBudget), ¬∀ v : M.Provenance, M.recall_cost v ≤ M.budget) →
      GroundedMitigates .boundedRecall .overbudgetReliance

/-! ## T27b Theorems -/

/-- GROUNDED MITIGATION IMPLIES DECLARED MITIGATION.

    Every proof-backed pairing in `GroundedMitigates` is also a declared pairing
    in `Mitigates`.  The implication is one-way: `Mitigates` constructors carry
    no proof payload, so the reverse does not hold without additional evidence.

    **Theorem shape:** `GroundedMitigates m r → Mitigates m r`
    **Proof strategy:** `cases` on the `GroundedMitigates` constructor; supply the
    matching `Mitigates` constructor directly. -/
theorem grounded_mitigation_implies_mitigation {m : EpArchMechanism} {r : ResidualRiskMode} :
    GroundedMitigates m r → Mitigates m r := by
  intro h
  cases h with
  | bubbles_scope_leak _          => exact .bubbles_scope_leak
  | standards_mismatch _          => exact .standards_mismatch
  | error_unmodeled _             => exact .error_unmodeled
  | provenance_gap _              => exact .provenance_gap
  | tau_staleness _               => exact .tau_staleness
  | auth_adversarial _            => exact .auth_adversarial
  | lifecycle_defect _            => exact .lifecycle_defect
  | bridge_overbudget _           => exact .bridge_overbudget
  | escalation_unsafe _           => exact .escalation_unsafe
  | redeemability_defect _        => exact .redeemability_defect
  | bounded_recall_overbudget _   => exact .bounded_recall_overbudget

/-- EPARCH SURFACE GROUNDEDLY COVERS RESIDUAL RISK MODES (T27b).

    Every residual-risk mode has a mitigation pairing backed by upstream theorem
    evidence or structural field-projection evidence.  This strengthens the
    declared coverage of T27a: the grounding confirms that each pairing is not
    merely a taxonomy claim but reflects structural or proof-level constraints
    in the formalization.

    **Theorem shape:** `∀ r : ResidualRiskMode, ∃ m : EpArchMechanism, GroundedMitigates m r`
    **Proof strategy:** `cases r`; supply the matching `GroundedMitigates` constructor
    with the actual proof witness for each mode.

    Evidence sources by mode:
    - `scopeLeak`          : `Deposit.bubble` field projection
    - `standardMismatch`   : `Header.S` field projection
    - `unmodeledError`     : `Header.E` field projection
    - `provenanceGap`      : `Header.V` field projection
    - `staleness`          : `PathExists.ttl_valid` — τ = 0 blocks any PathExists
    - `adversarialImport`  : `flat_authorization_impossible` (Minimality §7)
    - `unrevokedDefect`    : `challenge_produces_quarantined` (Bank.lean)
    - `overbudgetReliance` : `risk_not_eliminable_by_budgeted_bridge` (Minimality §11)
    - `unsafeAutonomy`     : `no_escalation_forces_bridge` (Health.lean T25)
    - `unrevokedDefect`    : `redeemable_implies_surface_aligned` (Commitments.lean)
                             (covered by `.redeemability` or `.bankLifecycle`)
    - `overbudgetReliance` : `recall_only_withdrawal_incomplete` (Minimality §9)
                             (covered by `.boundedRecall` or `.trustBridge`)

    Does not say: the mechanisms are irredundant or the surface is minimal.
    Does not say: the upstream theorems eliminate the underlying risk.
    Strict minimality / irredundancy is T28. -/
theorem eparch_surface_groundedly_covers_residual_risk_modes :
    ∀ r : ResidualRiskMode, ∃ m : EpArchMechanism, GroundedMitigates m r := by
  intro r; cases r with
  | scopeLeak =>
    exact ⟨.bubbles,
      .bubbles_scope_leak (fun PL S E P d => ⟨d.bubble, rfl⟩)⟩
  | standardMismatch =>
    exact ⟨.standardsHeader,
      .standards_mismatch (fun S E P h => ⟨h.S, rfl⟩)⟩
  | unmodeledError =>
    exact ⟨.errorHeader,
      .error_unmodeled (fun S E P h => ⟨h.E, rfl⟩)⟩
  | provenanceGap =>
    exact ⟨.provenanceHeader,
      .provenance_gap (fun S E P h => ⟨h.V, rfl⟩)⟩
  | staleness =>
    -- PathExists.ttl_valid : d.h.τ > 0; if τ = 0 then 0 > 0, contradiction via omega.
    exact ⟨.tau,
      .tau_staleness (fun PL S E P d h_zero pe =>
        absurd pe.ttl_valid (by simp [h_zero]))⟩
  | adversarialImport =>
    -- flat_authorization_impossible: no flat predicate represents both access tiers.
    exact ⟨.authorization,
      .auth_adversarial (fun M h => flat_authorization_impossible M h)⟩
  | unrevokedDefect =>
    -- challenge_produces_quarantined: deposited deposit is quarantined by Challenge_B.
    exact ⟨.bankLifecycle,
      .lifecycle_defect (fun PL S E P B d f h =>
        challenge_produces_quarantined B d f h)⟩
  | overbudgetReliance =>
    -- risk_not_eliminable_by_budgeted_bridge: budget-feasible bridge carries residual risk.
    exact ⟨.trustBridge,
      .bridge_overbudget (fun R b h_sim h_bud =>
        risk_not_eliminable_by_budgeted_bridge R b h_sim h_bud)⟩
  | unsafeAutonomy =>
    -- no_escalation_forces_bridge: without escalation, bridge is the only sound response.
    exact ⟨.escalation,
      .escalation_unsafe (fun M h_auto B d h_req h_fail h_no_esc =>
        no_escalation_forces_bridge M h_auto B d h_req h_fail h_no_esc)⟩

-- Note: T27a declared coverage (`eparch_surface_covers_residual_risk_modes`) is
-- already proved independently.  The derivation from T27b follows directly:
--   let ⟨m, hg⟩ := eparch_surface_groundedly_covers_residual_risk_modes r
--   ⟨m, grounded_mitigation_implies_mitigation hg⟩
-- A standalone theorem is omitted here because the call to
-- `eparch_surface_groundedly_covers_residual_risk_modes` introduces universe
-- parameters (from the `Deposit`/`redeemable` polymorphism in constructors)
-- that would also need to appear in the derived theorem's signature.  The
-- derivation is valid; the T27a theorem itself is the citable result.

end EpArch
